/*
    Copyright (C) 2026, Vincent Neiger, Éric Schost
    Copyright (C) 2026, Mael Hostettler

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include "fmpz.h"
#include "fmpz_vec.h"
#include "fmpz_mod.h"
#include "fmpz_mod_poly.h"

void _fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast_precomp(fmpz * poly,
            const fmpz * v, const fmpz_mod_geometric_progression_t G, slong len,
            const fmpz_mod_ctx_t ctx)
{
    FLINT_ASSERT(len <= G->len);
    FLINT_ASSERT((G->function & UWORD(2)) == UWORD(2));

    if (len == 1)
    {
        fmpz_set(poly, v);
        return;
    }

    /** step1: Newton interpolation
     * [Bostan - Schost, J.Complexity 2005, Section 5.1]
     * -> The coefficients of the interpolant, in the Newton basis associated
     *  to the geometric progression 1, q, q**2, q**3, etc., are obtained as
     *  c_0 / q_0, ..., c_{len-1} / q_{len-1}, where c_0, ..., c_{len-1} are
     *  the first coefficients of the product
     *     (sum_{i=0}^{len-1} v[i]/u_i x**i) (sum_{i=0}^{len-1} (-1)**i q_i/u_i x**i)
     *  where v[i] is the element at index `i` in the input values `v`,
     *  and u_i = prod_{1 <= k <= i} (q**k - 1),
     *  and q_i = q**(i*(i-1)/2)
     * -> With the precomputed data, these are the `len` coefficients of
     *    f * G->int_f  mod x**len
     * where f = sum_{i=0}^{len-1} v[i] * G->int_s1[i] x**i
     */

    /* val = valuation of output poly in Newton basis */
    slong val = 0;
    for (; val < len; val++)
        if (!fmpz_is_zero(v + val))
            break;
    if (val == len)
    {
        _fmpz_vec_zero(poly, len);
        return;
    }

    slong f_len, h_len;
    const slong f_alloc = len - val;
    fmpz * f = _fmpz_vec_init(f_alloc);
    fmpz * h = _fmpz_vec_init(len);

    /* actual length of f */
    for (f_len = len; f_len > val; f_len--)
        if (!fmpz_is_zero(v + f_len - 1))
            break;
    f_len = f_len - val;

    /* f = sum_{i=val}^{len-1} v[i] * G->int_s1[i] x**{i-val} */
    /*   == sum_{i=0}^{f_len-1} v[i+val] * G->int_s1[i+val] x**i */
    for (slong i = 0; i < f_len; i++)
        fmpz_mod_mul(f + i, v + i + val, G->int_s1 + i + val, ctx);

    /* h = (x**val * f) * G->int_f  mod x**len                     */
    /*   == x**val (f * G->int_f  mod x**(len-val))                */
    /* note: len - val is <= G->int_f->length, since G->int_f has  */
    /* length G->len >= len (all its coefficients are nonzero)     */
    _fmpz_mod_poly_mullow(h + val, G->int_f->coeffs, len - val, f, f_len, len - val, ctx);

    /* for Newton interpolation, here we should compute h[i] = h[i]/q_i */
    /* yet this "/q_i" will simplify with another operation just below, */
    /* so we just leave h as it is                                      */

    /** step2: Newton basis -> monomial basis
     * [Bostan - Schost, J.Complexity 2005, Section 5.2]
     * -> Convert h[i]/q_i to monomial basis, through the transposed
     *  x**len-truncated multiplication of two polynomials
     *       sum_{i=0}^{len-1} uu_i x**i
     *  and  sum_{i=0}^{len-1} (-1)**i * (h[i]/q_i)*q_i/uu_i x**i)
     *  where q_i = q**(i*(i-1)/2) as above,
     *  and uu_i = prod_{1 <= k <= i} q**(k-1) / (1 - q**k)
     *           == (-1)**i * q_i / u_i, for u_i as above
     *  (in the paper this is prod q**k / (1 - q**k), is this a typo?)
     *  This gives `len` coefficients that must then be scaled
     *  by (-1)**i * uu_i / q_i == 1 / u_i
     * -> Transposing the truncated product of poly1,poly2 of degree < len,
     *      mullow_t(res, poly1, poly2, len)
     *  simply amounts to a (non-tranposed) mullow and reversals:
     *      mullow(res, poly1, rev(poly2, len), len)
     *      res = rev(res, len)
     * -> With the precomputed data, the two polynomials have coefficients
     *     uu_i == G->int_f[i] and (-1)**i * h[i]/uu_i == h[i] * G->int_s2[i]
     *  meaning that we want to compute
     *          mullow_t(res, G->int_f, F, len)
     *   where F = sum_{i=0}^{len-1} h[i] * G->int_s2[i] x**i,
     *  and then scale by 1/u_i == G->int_s1[i]
     */

    /* valuation of h is at least val, see if it is higher */
    for (; val < len; val++)
        if (!fmpz_is_zero(h + val))
            break;

    /* actual length of h */
    for (h_len = len; h_len > val; h_len--)
        if (!fmpz_is_zero(h + h_len - 1))
            break;

    /* compute reversed and scaled f */
    for (slong i = 0; i < h_len - val; i++)
        fmpz_mod_mul(f + i, h + h_len - 1 - i, G->int_s2 + h_len - 1 - i, ctx);

    /* transposed short product */
    _fmpz_mod_poly_mullow(h + len - h_len, G->int_f->coeffs, h_len, f, h_len - val, h_len, ctx);

    /* final scaling */
    _fmpz_vec_zero(poly + h_len, len - h_len);
    for (slong i = 0; i < h_len; i++)
        fmpz_mod_mul(poly + i, h + len - 1 - i, G->int_s1 + i, ctx);

    _fmpz_vec_clear(f, f_alloc);
    _fmpz_vec_clear(h, len);
}

void fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast_precomp(fmpz_mod_poly_t poly,
                const fmpz * v, const fmpz_mod_geometric_progression_t G, slong len,
                const fmpz_mod_ctx_t ctx)
{
    FLINT_ASSERT((G->function & UWORD(2)) == UWORD(2));

    fmpz_mod_poly_fit_length(poly, len, ctx);
    _fmpz_mod_poly_set_length(poly, len);
    _fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast_precomp(poly->coeffs, v, G, len, ctx);
    _fmpz_mod_poly_normalise(poly);
}

void fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast(fmpz_mod_poly_t poly,
                const fmpz_t r, const fmpz * ys, slong len, const fmpz_mod_ctx_t ctx)
{
    fmpz_mod_geometric_progression_t G;
    _fmpz_mod_geometric_progression_init_function(G, r, len, UWORD(2), ctx);
    fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast_precomp(poly, ys, G, len, ctx);
    fmpz_mod_geometric_progression_clear(G, ctx);
}
