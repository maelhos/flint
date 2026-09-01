/*
    Copyright (C) 2026 Mael Hostettler
    Copyright (C) 2026 Antoine Bak
    Copyright (C) 2026 Vincent Neiger

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include "mpn_extras.h"
#include "nmod.h"
#include "nmod_vec.h"
#include "nmod_poly.h"
#include "gr_poly.h"

/* Number of geometric progressions tried before giving up. */
#define RESULTANT_MULTIPOINT_ATTEMPTS 5

/* Target size, in words, of the tables holding the evaluated coefficients.
   The evaluation points are processed in blocks chosen so that these tables
   stay around this size; the memory usage is then proportional to the input
   and output sizes instead of to their product. */
#define RESULTANT_MULTIPOINT_BLOCK_WORDS (WORD(1) << 18)

/* Returns 1 if none of q, q^2, ..., q^(len-1) is one, i.e. if the len
   points 1, q, q^2, ..., q^(len-1) are pairwise distinct. */
static int
_nmod_geometric_points_distinct(ulong q, slong len, nmod_t mod)
{
    ulong qi = 1;
    slong i;

    for (i = 1; i < len; i++)
    {
        qi = nmod_mul(qi, q, mod);

        if (qi == 1)
            return 0;
    }

    return 1;
}

int
_gr_poly_resultant_multipoint(gr_ptr res, gr_srcptr A, slong lenA,
                              gr_srcptr B, slong lenB, gr_ctx_t ctx)
{
    const gr_poly_struct * Ax = A;
    const gr_poly_struct * Bx = B;
    gr_poly_struct * resx = res;
    gr_ctx_struct * cctx;
    nmod_geometric_progression_t G;
    flint_rand_t state;
    nmod_t mod;
    nn_ptr valA, valB, valres, resc, tmp, spow, w, f, g;
    slong i, j, k, blenA, blenB, npoints, maxlen, batch, nblocks, block;
    ulong c, cinv, r, q, t;
    int attempt, ok;

    if (ctx->which_ring != GR_CTX_GR_POLY)
        return GR_UNABLE;

    cctx = POLYNOMIAL_ELEM_CTX(ctx);

    if (cctx->which_ring != GR_CTX_NMOD)
        return GR_UNABLE;

    if (lenB <= 1)
        return _gr_poly_resultant_small(res, A, lenA, B, lenB, ctx);

    /* Leading coefficients in y must be nonzero for the degree bound and the
       specialisation property to hold. */
    if (Ax[lenA - 1].length == 0 || Bx[lenB - 1].length == 0)
        return GR_UNABLE;

    /* blenA - 1 and blenB - 1 bound the degrees in x */
    blenA = 0;
    for (i = 0; i < lenA; i++)
        blenA = FLINT_MAX(blenA, Ax[i].length);

    blenB = 0;
    for (i = 0; i < lenB; i++)
        blenB = FLINT_MAX(blenB, Bx[i].length);

    /* deg_x(res) <= deg_y(B) deg_x(A) + deg_y(A) deg_x(B); note that this
       makes npoints >= maxlen, since lenA, lenB >= 2 */
    npoints = (lenB - 1) * (blenA - 1) + (lenA - 1) * (blenB - 1) + 1;
    maxlen = FLINT_MAX(blenA, blenB);

    mod = NMOD_CTX(cctx);

    /* We need an element of multiplicative order at least npoints, and the
       precomputations assume that the modulus is prime. */
    if (mod.n <= (ulong) npoints || gr_ctx_is_field(cctx) != T_TRUE)
        return GR_UNABLE;

    /* The points are handled in blocks of `batch` of them. Evaluating a
       coefficient of length maxlen at fewer than maxlen points saves nothing,
       so that is the smallest useful block; above that, the block is as large
       as the memory target allows. */
    batch = FLINT_MAX(maxlen, RESULTANT_MULTIPOINT_BLOCK_WORDS / (lenA + lenB));
    batch = FLINT_MIN(batch, npoints);
    nblocks = (npoints + batch - 1) / batch;

    valA = _nmod_vec_init(lenA * batch);
    valB = _nmod_vec_init(lenB * batch);
    valres = _nmod_vec_init(npoints);
    resc = _nmod_vec_init(npoints);
    tmp = _nmod_vec_init(maxlen);
    spow = _nmod_vec_init(maxlen);
    w = _nmod_vec_init(maxlen);
    f = _nmod_vec_init(lenA + lenB);
    g = f + lenA;

    /* The seed is fixed, so that this function is deterministic. */
    flint_rand_init(state);

    /* The evaluation points are c, c q, c q^2, ..., c q^(npoints-1), where
       q = r^2 and both r and c are chosen at random. The block starting at
       index k*batch consists of the points s q^i for 0 <= i < batch, with
       s = c q^(k*batch); the substitution x -> s x on the input polynomials
       turns those into the powers of q that the geometric progression
       provides, so a single precomputation of length batch serves for all
       blocks. The leading coefficient of A in y must not vanish at any of
       the points; if it does, we start over with a new progression, giving
       up after RESULTANT_MULTIPOINT_ATTEMPTS tries. */
    ok = 0;

    for (attempt = 0; attempt < RESULTANT_MULTIPOINT_ATTEMPTS; attempt++)
    {
        r = 1 + n_randint(state, mod.n - 1);
        q = nmod_mul(r, r, mod);

        if (!_nmod_geometric_points_distinct(q, npoints, mod))
            continue;

        c = 1 + n_randint(state, mod.n - 1);

        /* spow[j] = s^j for the current block, starting with s = c;
           multiplying by w[j] = (q^batch)^j advances s by one block */
        t = nmod_pow_ui(q, batch, mod);
        spow[0] = 1;
        w[0] = 1;
        for (j = 1; j < maxlen; j++)
        {
            spow[j] = nmod_mul(spow[j - 1], c, mod);
            w[j] = nmod_mul(w[j - 1], t, mod);
        }

        _nmod_geometric_progression_init_function(G, r, batch, mod, UWORD(1));

        ok = 1;

        for (block = 0; block < nblocks; block++)
        {
            slong blen = FLINT_MIN(batch, npoints - block * batch);

            for (i = 0; i < lenA; i++)
            {
                for (k = 0; k < Ax[i].length; k++)
                    tmp[k] = nmod_mul(((nn_srcptr) Ax[i].coeffs)[k], spow[k], mod);

                _nmod_poly_evaluate_geometric_nmod_vec_fast_precomp(valA + i * batch,
                    tmp, Ax[i].length, G, blen, mod);
            }

            for (j = 0; j < blen; j++)
            {
                if (valA[(lenA - 1) * batch + j] == 0)
                {
                    ok = 0;
                    break;
                }
            }

            if (!ok)
                break;

            for (i = 0; i < lenB; i++)
            {
                for (k = 0; k < Bx[i].length; k++)
                    tmp[k] = nmod_mul(((nn_srcptr) Bx[i].coeffs)[k], spow[k], mod);

                _nmod_poly_evaluate_geometric_nmod_vec_fast_precomp(valB + i * batch,
                    tmp, Bx[i].length, G, blen, mod);
            }

            for (j = 0; j < blen; j++)
            {
                slong len2;

                for (i = 0; i < lenA; i++)
                    f[i] = valA[i * batch + j];

                for (i = 0; i < lenB; i++)
                    g[i] = valB[i * batch + j];

                len2 = lenB;
                MPN_NORM(g, len2);

                if (len2 == 0)
                {
                    valres[block * batch + j] = 0;
                }
                else
                {
                    t = _nmod_poly_resultant(f, lenA, g, len2, mod);

                    /* the specialisation of B may drop in degree, in which case
                       res(A, B)(x) = lc_y(A)(x)^(lenB - len2) res(A(x), B(x)) */
                    if (len2 < lenB)
                        t = nmod_mul(t, nmod_pow_ui(f[lenA - 1], lenB - len2, mod), mod);

                    valres[block * batch + j] = t;
                }
            }

            for (k = 1; k < maxlen; k++)
                spow[k] = nmod_mul(spow[k], w[k], mod);
        }

        nmod_geometric_progression_clear(G);

        if (ok)
            break;
    }

    if (ok)
    {
        _nmod_geometric_progression_init_function(G, r, npoints, mod, UWORD(2));
        _nmod_poly_interpolate_geometric_nmod_vec_fast_precomp(resc, valres, G, npoints, mod);
        nmod_geometric_progression_clear(G);

        /* undo the scaling by c */
        cinv = nmod_inv(c, mod);
        t = 1;
        for (k = 0; k < npoints; k++)
        {
            resc[k] = nmod_mul(resc[k], t, mod);
            t = nmod_mul(t, cinv, mod);
        }

        gr_poly_fit_length(resx, npoints, cctx);
        _gr_poly_set_length(resx, npoints, cctx);
        _nmod_vec_set((nn_ptr) resx->coeffs, resc, npoints);
        _gr_poly_normalise(resx, cctx);
    }

    flint_rand_clear(state);

    _nmod_vec_clear(valA);
    _nmod_vec_clear(valB);
    _nmod_vec_clear(valres);
    _nmod_vec_clear(resc);
    _nmod_vec_clear(tmp);
    _nmod_vec_clear(spow);
    _nmod_vec_clear(w);
    _nmod_vec_clear(f);

    return ok ? GR_SUCCESS : GR_UNABLE;
}

int
gr_poly_resultant_multipoint(gr_ptr r, const gr_poly_t f,
                             const gr_poly_t g, gr_ctx_t ctx)
{
    slong len1 = f->length;
    slong len2 = g->length;
    int status = GR_SUCCESS;
    slong sz = ctx->sizeof_elem;

    if (len1 == 0 || len2 == 0)
    {
        return gr_zero(r, ctx);
    }

    if (gr_is_zero(GR_ENTRY(f->coeffs, len1 - 1, sz), ctx) != T_FALSE ||
        gr_is_zero(GR_ENTRY(g->coeffs, len2 - 1, sz), ctx) != T_FALSE)
    {
        return GR_UNABLE;
    }

    if (len1 >= len2)
    {
        status |= _gr_poly_resultant_multipoint(r, f->coeffs, len1, g->coeffs, len2, ctx);
    }
    else
    {
        status |= _gr_poly_resultant_multipoint(r, g->coeffs, len2, f->coeffs, len1, ctx);

        if (((len1 | len2) & 1) == 0)
            status |= gr_neg(r, r, ctx);
    }

    return status;
}
