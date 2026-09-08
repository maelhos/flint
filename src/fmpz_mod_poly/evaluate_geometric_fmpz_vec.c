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

void _fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast_precomp(fmpz * vs, const fmpz * poly, slong plen,
                                                             const fmpz_mod_geometric_progression_t G, slong len,
                                                             const fmpz_mod_ctx_t ctx)
{
    FLINT_ASSERT(G->function & 1);
    FLINT_ASSERT(len <= G->len);

    /* val = valuation of poly */
    slong val = 0;
    for ( ; val < plen; val++)
    {
        if (!fmpz_is_zero(poly + val))
        {
            break;
        }
    }

    if (val == plen) /* covers the case plen == 0 */
    {
        _fmpz_vec_zero(vs, len);
        return;
    }

    /** Formula, based on Bluestein's trick:
     * poly(q**j) = sum_{i=0}^{n-1} poly[i] q**{i*j}  is the coefficient x**{n+j-1} of the product
     *     (sum_{i=0}^{len-1} poly[i] * q**(-i*i / 2) x**{len-i-1}) * (sum_{i=0}^{2*len-2} q**{i*i/2} x**i)
     * -> the right-hand polynomial is G->ev_f truncated at precision 2*len - 1
     * -> the inverses q**(-i*i / 2) are the first len values stored in G->ev_s
     *
     * Thus, goal is to compute [rev(p) * G->ev_f]_{plen - 1}^{len}, where p is poly scaled by G->ev_s
     * (the bracket notation means coefficients [plen - 1, plen - 1 + len))
     * If p has valuation val, define a = p / x**val of length alen = plen - val, and this becomes
     * [rev(a) * (G->ev_f >> x**val)]_{alen - 1}^{len}  (that is, coeffs [alen - 1, alen - 1 + len))
     */

    const slong alen = plen - val;

    fmpz * a = _fmpz_vec_init(alen);
    fmpz * b = _fmpz_vec_init(alen - 1 + len);

    for (slong i = val; i < plen; i++)
        fmpz_mod_mul(a + plen - 1 - i, G->ev_s + i, poly + i, ctx);

    _fmpz_mod_poly_mulmid(b, G->ev_f->coeffs + val, alen - 1 + len, a, alen, alen - 1, alen - 1 + len, ctx);

    for (slong i = 0; i < len; i++)
        fmpz_mod_mul(vs + i, G->ev_s + i, b + i, ctx);

    _fmpz_vec_clear(a, alen);
    _fmpz_vec_clear(b, alen - 1 + len);
}

void _fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(fmpz * ys, const fmpz * poly, slong plen,
                                                     const fmpz_t r, slong n, const fmpz_mod_ctx_t ctx)
{
    if (n == 0)
        return;

    fmpz_mod_geometric_progression_t G;
    _fmpz_mod_geometric_progression_init_function(G, r, FLINT_MAX(n, plen), UWORD(1), ctx);
    _fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast_precomp(ys, poly, plen, G, n, ctx);
    fmpz_mod_geometric_progression_clear(G, ctx);
}

void fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(fmpz * ys, const fmpz_mod_poly_t poly,
                                                    const fmpz_t r, slong n, const fmpz_mod_ctx_t ctx)
{
    _fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(ys, poly->coeffs, poly->length, r, n, ctx);
}

void _fmpz_mod_poly_evaluate_geometric_fmpz_vec_iter(fmpz * ys, const fmpz * coeffs, slong len,
                                                     const fmpz_t r, slong n, const fmpz_mod_ctx_t ctx)
{
    slong i;
    fmpz_t rpow, r2;

    fmpz_init_set_ui(rpow, 1);
    fmpz_init(r2);

    fmpz_mod_mul(r2, r, r, ctx);

    for (i = 0; i < n; i++)
    {
        _fmpz_mod_poly_evaluate_fmpz(ys + i, coeffs, len, rpow, ctx);
        fmpz_mod_mul(rpow, rpow, r2, ctx);
    }

    fmpz_clear(rpow);
    fmpz_clear(r2);
}

void fmpz_mod_poly_evaluate_geometric_fmpz_vec_iter(fmpz * ys, const fmpz_mod_poly_t poly,
                                                    const fmpz_t r, slong n, const fmpz_mod_ctx_t ctx)
{
    _fmpz_mod_poly_evaluate_geometric_fmpz_vec_iter(ys, poly->coeffs, poly->length, r, n, ctx);
}
