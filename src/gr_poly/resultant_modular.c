/*
    Copyright (C) 2026 Mael Hostettler

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include "fmpz.h"
#include "fmpz_vec.h"
#include "fmpz_poly.h"
#include "fmpq.h"
#include "nmod.h"
#include "nmod_vec.h"
#include "ulong_extras.h"
#include "gr_poly.h"

/* Bits of the primes used for the modular images. Staying below
   FLINT_BITS - 1 keeps NMOD_CAN_USE_SHOUP true for the images. */
#define MODULAR_PRIME_BITS (FLINT_BITS - 2)

/* Bound for the coefficients of res_y(A, B), where A and B are seen as
   polynomials in y with coefficients in Z[x]:

      ||res||_oo <= (sum_i ||A_i||_1^2)^(n/2) (sum_j ||B_j||_1^2)^(m/2)

   with m = deg_y(A) and n = deg_y(B). The coefficients of the resultant are
   bounded by its maximum modulus on the unit circle |x| = 1, where the
   univariate bound |res(F, G)| <= ||F||_2^deg(G) ||G||_2^deg(F) applies with
   ||A(x, .)||_2^2 = sum_i |A_i(x)|^2 <= sum_i ||A_i||_1^2. */
static void
_bivariate_resultant_bound(fmpz_t bound,
                           const fmpz_poly_struct * A, slong lenA,
                           const fmpz_poly_struct * B, slong lenB)
{
    fmpz_t sa, sb, t, u;
    slong i, k;

    fmpz_init(sa);
    fmpz_init(sb);
    fmpz_init(t);
    fmpz_init(u);

    for (i = 0; i < lenA; i++)
    {
        fmpz_zero(t);
        for (k = 0; k < A[i].length; k++)
        {
            fmpz_abs(u, A[i].coeffs + k);
            fmpz_add(t, t, u);
        }
        fmpz_addmul(sa, t, t);
    }

    for (i = 0; i < lenB; i++)
    {
        fmpz_zero(t);
        for (k = 0; k < B[i].length; k++)
        {
            fmpz_abs(u, B[i].coeffs + k);
            fmpz_add(t, t, u);
        }
        fmpz_addmul(sb, t, t);
    }

    fmpz_pow_ui(sa, sa, lenB - 1);
    fmpz_pow_ui(sb, sb, lenA - 1);
    fmpz_mul(bound, sa, sb);
    fmpz_sqrt(bound, bound);
    fmpz_add_ui(bound, bound, 1);

    fmpz_clear(sa);
    fmpz_clear(sb);
    fmpz_clear(t);
    fmpz_clear(u);
}

/* res_y(A, B) mod p, written to (out, outlen) with zero padding. A and B must
   have nonzero leading coefficients mod p, so that the degrees in y are
   preserved and the reduction commutes with the resultant. The gr_poly
   structures are supplied by the caller and reused across primes; the element
   layout over nmod does not depend on the modulus. */
static int
_bivariate_resultant_nmod(nn_ptr out, slong outlen,
                          const fmpz_poly_struct * A, slong lenA,
                          const fmpz_poly_struct * B, slong lenB, ulong p,
                          gr_poly_struct * Ap, gr_poly_struct * Bp, gr_poly_t rp)
{
    gr_ctx_t cctx, ctx;
    slong i, k, len;
    int status;

    gr_ctx_init_nmod(cctx, p);
    GR_MUST_SUCCEED(gr_ctx_set_is_field(cctx, T_TRUE));
    gr_ctx_init_gr_poly(ctx, cctx);

    for (i = 0; i < lenA; i++)
    {
        for (k = 0; k < A[i].length; k++)
            ((nn_ptr) Ap[i].coeffs)[k] = fmpz_fdiv_ui(A[i].coeffs + k, p);
        len = A[i].length;
        while (len > 0 && ((nn_srcptr) Ap[i].coeffs)[len - 1] == 0)
            len--;
        Ap[i].length = len;
    }

    for (i = 0; i < lenB; i++)
    {
        for (k = 0; k < B[i].length; k++)
            ((nn_ptr) Bp[i].coeffs)[k] = fmpz_fdiv_ui(B[i].coeffs + k, p);
        len = B[i].length;
        while (len > 0 && ((nn_srcptr) Bp[i].coeffs)[len - 1] == 0)
            len--;
        Bp[i].length = len;
    }

    status = _gr_poly_resultant(rp, Ap, lenA, Bp, lenB, ctx);

    if (status == GR_SUCCESS)
    {
        for (k = 0; k < outlen; k++)
            out[k] = (k < rp->length) ? ((nn_srcptr) rp->coeffs)[k] : 0;
    }

    gr_ctx_clear(ctx);
    gr_ctx_clear(cctx);

    return status;
}

/* CRT the residues of `len` coefficients, laid out prime-major with the given
   stride, over the first `num` primes. */
static void
_crt_reconstruct(fmpz * out, slong len, nn_srcptr residues, slong stride,
                 nn_srcptr primes, slong num)
{
    fmpz_comb_t comb;
    fmpz_comb_temp_t temp;
    nn_ptr r;
    slong i, k;

    r = flint_malloc(num * sizeof(ulong));

    fmpz_comb_init(comb, primes, num);
    fmpz_comb_temp_init(temp, comb);

    for (k = 0; k < len; k++)
    {
        for (i = 0; i < num; i++)
            r[i] = residues[i * stride + k];

        fmpz_multi_CRT_ui(out + k, r, comb, temp, 1);
    }

    fmpz_comb_temp_clear(temp);
    fmpz_comb_clear(comb);
    flint_free(r);
}

/* res_y(A, B) over Z. A and B are working copies which are modified. */
static int
_fmpz_bivariate_resultant(fmpz_poly_t res,
                          fmpz_poly_struct * A, slong lenA,
                          fmpz_poly_struct * B, slong lenB)
{
    fmpz_poly_t pa, pb, t;
    fmpz_t ca, cb, l, bound, modulus, probe, probe_prev, u;
    flint_rand_t state;
    nn_ptr residues, primes, r, v, Abuf, Bbuf;
    gr_poly_struct * Ap, * Bp;
    gr_poly_t rp;
    gr_ctx_t tctx;
    fmpz * cand;
    slong totA, totB;
    slong i, k, dxA, dxB, outlen, num, alloc;
    flint_bitcnt_t bound_bits, curr_bits;
    ulong p;
    int status = GR_SUCCESS;
    int checking, done;

    fmpz_init(ca);
    fmpz_init(cb);
    fmpz_init(l);
    fmpz_init(u);
    fmpz_poly_init(pa);
    fmpz_poly_init(pb);
    fmpz_poly_init(t);

    /* integer contents */
    for (i = 0; i < lenA; i++)
        _fmpz_vec_content_chained(ca, A[i].coeffs, A[i].length, ca);
    if (!fmpz_is_one(ca))
        for (i = 0; i < lenA; i++)
            fmpz_poly_scalar_divexact_fmpz(A + i, A + i, ca);

    for (i = 0; i < lenB; i++)
        _fmpz_vec_content_chained(cb, B[i].coeffs, B[i].length, cb);
    if (!fmpz_is_one(cb))
        for (i = 0; i < lenB; i++)
            fmpz_poly_scalar_divexact_fmpz(B + i, B + i, cb);

    /* contents in x; res(c(x) A, B) = c(x)^deg_y(B) res(A, B) */
    for (i = 0; i < lenA; i++)
    {
        fmpz_poly_gcd(pa, pa, A + i);
        if (pa->length == 1)
            break;
    }
    if (pa->length > 1)
        for (i = 0; i < lenA; i++)
            fmpz_poly_divexact(A + i, A + i, pa);

    for (i = 0; i < lenB; i++)
    {
        fmpz_poly_gcd(pb, pb, B + i);
        if (pb->length == 1)
            break;
    }
    if (pb->length > 1)
        for (i = 0; i < lenB; i++)
            fmpz_poly_divexact(B + i, B + i, pb);

    /* a prime must not divide the leading coefficient in y of either input,
       or the degree in y would drop in the modular image */
    _fmpz_vec_content(l, A[lenA - 1].coeffs, A[lenA - 1].length);
    _fmpz_vec_content(u, B[lenB - 1].coeffs, B[lenB - 1].length);
    fmpz_mul(l, l, u);

    dxA = 0;
    for (i = 0; i < lenA; i++)
        dxA = FLINT_MAX(dxA, A[i].length);
    dxB = 0;
    for (i = 0; i < lenB; i++)
        dxB = FLINT_MAX(dxB, B[i].length);

    /* deg_x(res) <= deg_y(B) deg_x(A) + deg_y(A) deg_x(B) */
    outlen = (lenB - 1) * (dxA - 1) + (lenA - 1) * (dxB - 1) + 1;

    fmpz_init(bound);
    _bivariate_resultant_bound(bound, A, lenA, B, lenB);
    bound_bits = fmpz_bits(bound) + 2;

    fmpz_init_set_ui(modulus, 1);
    fmpz_init(probe);
    fmpz_init(probe_prev);

    flint_rand_init(state);

    /* Random weights for the probe: instead of reconstructing every
       coefficient after each prime, only the single integer sum_k v_k res_k is
       tracked, and a full reconstruction is attempted when it stops changing.
       A probe can stabilise early by accident, so the candidate is always
       verified against a fresh prime before being accepted. */
    v = flint_malloc(outlen * sizeof(ulong));
    for (k = 0; k < outlen; k++)
        v[k] = 1 + n_randint(state, UWORD(1) << 20);

    /* modular images, reused across primes */
    totA = 0;
    for (i = 0; i < lenA; i++)
        totA += A[i].length;
    totB = 0;
    for (i = 0; i < lenB; i++)
        totB += B[i].length;

    Abuf = _nmod_vec_init(FLINT_MAX(totA, 1));
    Bbuf = _nmod_vec_init(FLINT_MAX(totB, 1));
    Ap = flint_malloc(lenA * sizeof(gr_poly_struct));
    Bp = flint_malloc(lenB * sizeof(gr_poly_struct));

    totA = 0;
    for (i = 0; i < lenA; i++)
    {
        Ap[i].coeffs = Abuf + totA;
        Ap[i].alloc = A[i].length;
        Ap[i].length = 0;
        totA += A[i].length;
    }
    totB = 0;
    for (i = 0; i < lenB; i++)
    {
        Bp[i].coeffs = Bbuf + totB;
        Bp[i].alloc = B[i].length;
        Bp[i].length = 0;
        totB += B[i].length;
    }

    gr_ctx_init_nmod(tctx, UWORD(2));
    gr_poly_init(rp, tctx);

    alloc = 16;
    residues = flint_malloc(alloc * outlen * sizeof(ulong));
    primes = flint_malloc(alloc * sizeof(ulong));
    cand = _fmpz_vec_init(outlen);

    p = (UWORD(1) << MODULAR_PRIME_BITS) - n_randint(state, UWORD(1) << 20);
    num = 0;
    curr_bits = 0;
    checking = 0;
    done = 0;

    while (!done && curr_bits < bound_bits)
    {
        nmod_t mod;
        ulong s;

        p = n_nextprime(p, 0);
        if (fmpz_fdiv_ui(l, p) == 0)
            continue;

        if (num == alloc)
        {
            alloc *= 2;
            residues = flint_realloc(residues, alloc * outlen * sizeof(ulong));
            primes = flint_realloc(primes, alloc * sizeof(ulong));
        }

        r = residues + num * outlen;
        status = _bivariate_resultant_nmod(r, outlen, A, lenA, B, lenB, p, Ap, Bp, rp);

        if (status != GR_SUCCESS)
            break;

        /* the prime just computed verifies the pending candidate */
        if (checking)
        {
            int agree = 1;

            for (k = 0; k < outlen; k++)
            {
                if (fmpz_fdiv_ui(cand + k, p) != r[k])
                {
                    agree = 0;
                    break;
                }
            }

            if (agree)
            {
                done = 1;
                break;
            }

            checking = 0;
        }

        primes[num] = p;
        num++;
        curr_bits += MODULAR_PRIME_BITS;

        nmod_init(&mod, p);
        s = 0;
        for (k = 0; k < outlen; k++)
            s = nmod_add(s, nmod_mul(v[k], r[k], mod), mod);

        fmpz_CRT_ui(probe, probe, modulus, s, p, 1);
        fmpz_mul_ui(modulus, modulus, p);

        if (num >= 2 && fmpz_equal(probe, probe_prev))
        {
            _crt_reconstruct(cand, outlen, residues, outlen, primes, num);
            checking = 1;
        }

        fmpz_set(probe_prev, probe);
    }

    if (status == GR_SUCCESS)
    {
        /* the bound was reached without the probe settling */
        if (!done)
            _crt_reconstruct(cand, outlen, residues, outlen, primes, num);

        fmpz_poly_fit_length(res, outlen);
        for (k = 0; k < outlen; k++)
            fmpz_swap(res->coeffs + k, cand + k);
        _fmpz_poly_set_length(res, outlen);
        _fmpz_poly_normalise(res);

        /* put back the contents removed above */
        fmpz_pow_ui(ca, ca, lenB - 1);
        fmpz_pow_ui(cb, cb, lenA - 1);
        fmpz_mul(ca, ca, cb);
        fmpz_poly_scalar_mul_fmpz(res, res, ca);

        if (pa->length > 1)
        {
            fmpz_poly_pow(t, pa, lenB - 1);
            fmpz_poly_mul(res, res, t);
        }

        if (pb->length > 1)
        {
            fmpz_poly_pow(t, pb, lenA - 1);
            fmpz_poly_mul(res, res, t);
        }
    }

    flint_rand_clear(state);

    gr_poly_clear(rp, tctx);
    gr_ctx_clear(tctx);
    _nmod_vec_clear(Abuf);
    _nmod_vec_clear(Bbuf);
    flint_free(Ap);
    flint_free(Bp);

    _fmpz_vec_clear(cand, outlen);
    flint_free(residues);
    flint_free(primes);
    flint_free(v);

    fmpz_clear(ca);
    fmpz_clear(cb);
    fmpz_clear(l);
    fmpz_clear(u);
    fmpz_clear(bound);
    fmpz_clear(modulus);
    fmpz_clear(probe);
    fmpz_clear(probe_prev);
    fmpz_poly_clear(pa);
    fmpz_poly_clear(pb);
    fmpz_poly_clear(t);

    return status;
}

int
_gr_poly_resultant_modular(gr_ptr res, gr_srcptr A, slong lenA,
                           gr_srcptr B, slong lenB, gr_ctx_t ctx)
{
    const gr_poly_struct * Ax = A;
    const gr_poly_struct * Bx = B;
    gr_poly_struct * resx = res;
    gr_ctx_struct * cctx;
    fmpz_poly_struct * Az, * Bz;
    fmpz_poly_t R;
    fmpz_t da, db, t;
    slong i, k;
    int rational;
    int status;

    if (ctx->which_ring != GR_CTX_GR_POLY)
        return GR_UNABLE;

    cctx = POLYNOMIAL_ELEM_CTX(ctx);

    if (cctx->which_ring == GR_CTX_FMPZ)
        rational = 0;
    else if (cctx->which_ring == GR_CTX_FMPQ)
        rational = 1;
    else
        return GR_UNABLE;

    if (lenB <= 1)
        return _gr_poly_resultant_small(res, A, lenA, B, lenB, ctx);

    if (Ax[lenA - 1].length == 0 || Bx[lenB - 1].length == 0)
        return GR_UNABLE;

    fmpz_init_set_ui(da, 1);
    fmpz_init_set_ui(db, 1);
    fmpz_init(t);

    Az = flint_malloc(lenA * sizeof(fmpz_poly_struct));
    Bz = flint_malloc(lenB * sizeof(fmpz_poly_struct));

    for (i = 0; i < lenA; i++)
        fmpz_poly_init(Az + i);
    for (i = 0; i < lenB; i++)
        fmpz_poly_init(Bz + i);

    if (!rational)
    {
        /* a gr_poly over fmpz has the same layout as an fmpz_poly */
        for (i = 0; i < lenA; i++)
            fmpz_poly_set(Az + i, (const fmpz_poly_struct *) (Ax + i));
        for (i = 0; i < lenB; i++)
            fmpz_poly_set(Bz + i, (const fmpz_poly_struct *) (Bx + i));
    }
    else
    {
        /* clear denominators; res(A/da, B/db) = res(A, B) / (da^n db^m) */
        for (i = 0; i < lenA; i++)
            for (k = 0; k < Ax[i].length; k++)
                fmpz_lcm(da, da, fmpq_denref(((const fmpq *) Ax[i].coeffs) + k));

        for (i = 0; i < lenB; i++)
            for (k = 0; k < Bx[i].length; k++)
                fmpz_lcm(db, db, fmpq_denref(((const fmpq *) Bx[i].coeffs) + k));

        for (i = 0; i < lenA; i++)
        {
            fmpz_poly_fit_length(Az + i, Ax[i].length);
            for (k = 0; k < Ax[i].length; k++)
            {
                const fmpq * c = ((const fmpq *) Ax[i].coeffs) + k;
                fmpz_divexact(t, da, fmpq_denref(c));
                fmpz_mul(Az[i].coeffs + k, fmpq_numref(c), t);
            }
            _fmpz_poly_set_length(Az + i, Ax[i].length);
            _fmpz_poly_normalise(Az + i);
        }

        for (i = 0; i < lenB; i++)
        {
            fmpz_poly_fit_length(Bz + i, Bx[i].length);
            for (k = 0; k < Bx[i].length; k++)
            {
                const fmpq * c = ((const fmpq *) Bx[i].coeffs) + k;
                fmpz_divexact(t, db, fmpq_denref(c));
                fmpz_mul(Bz[i].coeffs + k, fmpq_numref(c), t);
            }
            _fmpz_poly_set_length(Bz + i, Bx[i].length);
            _fmpz_poly_normalise(Bz + i);
        }
    }

    fmpz_poly_init(R);
    status = _fmpz_bivariate_resultant(R, Az, lenA, Bz, lenB);

    if (status == GR_SUCCESS)
    {
        gr_poly_fit_length(resx, R->length, cctx);

        if (!rational)
        {
            for (k = 0; k < R->length; k++)
                fmpz_set(((fmpz *) resx->coeffs) + k, R->coeffs + k);
        }
        else
        {
            fmpz_pow_ui(da, da, lenB - 1);
            fmpz_pow_ui(db, db, lenA - 1);
            fmpz_mul(da, da, db);

            for (k = 0; k < R->length; k++)
                fmpq_set_fmpz_frac(((fmpq *) resx->coeffs) + k, R->coeffs + k, da);
        }

        _gr_poly_set_length(resx, R->length, cctx);
        _gr_poly_normalise(resx, cctx);
    }

    fmpz_poly_clear(R);

    for (i = 0; i < lenA; i++)
        fmpz_poly_clear(Az + i);
    for (i = 0; i < lenB; i++)
        fmpz_poly_clear(Bz + i);

    flint_free(Az);
    flint_free(Bz);

    fmpz_clear(da);
    fmpz_clear(db);
    fmpz_clear(t);

    return status;
}

int
gr_poly_resultant_modular(gr_ptr r, const gr_poly_t f,
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
        status |= _gr_poly_resultant_modular(r, f->coeffs, len1, g->coeffs, len2, ctx);
    }
    else
    {
        status |= _gr_poly_resultant_modular(r, g->coeffs, len2, f->coeffs, len1, ctx);

        if (((len1 | len2) & 1) == 0)
            status |= gr_neg(r, r, ctx);
    }

    return status;
}
