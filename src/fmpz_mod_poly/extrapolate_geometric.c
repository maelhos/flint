/*
    Copyright (C) 2026 Vincent Neiger, Kevin Tran
    Copyright (C) 2026 Maël Hostettler

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

void fmpz_mod_poly_extrapolate_geometric_precomp(fmpz * oval, slong olen,
                                                 const fmpz * ival, slong ilen,
                                                 slong offset,
                                                 const fmpz_mod_geometric_progression_t G,
                                                 const fmpz_mod_ctx_t ctx)
{
    /* precomputation has been done */
    FLINT_ASSERT((G->function & UWORD(4)) == UWORD(4));
    /* input/output points are disjoint, and stay within precomputed data length */
    FLINT_ASSERT((offset >= ilen && G->len >= offset+olen)
                 || (offset <= -olen && G->len >= ilen-offset));

    if (olen == 0)
        return;

    if (ilen == 0)
    {
        _fmpz_vec_zero(oval, olen);
        return;
    }

    if (ilen == 1)
    {
        for (slong i = 0; i < olen; i++)
            fmpz_set(oval + i, ival);
        return;
    }

    /* forward extrapolation */
    if (offset > 0)
    {
        fmpz * tmp = _fmpz_vec_init(ilen);

        /* first scaling */
        for (slong i = 0; i < ilen; i++)
        {
            fmpz_mod_mul(tmp + i, G->ext_s3 + ilen-1-i, ival + i, ctx);
            fmpz_mod_mul(tmp + i, G->ext_s2 + i, tmp + i, ctx);
        }

        /* middle product */
        _fmpz_mod_poly_mulmid(oval, G->ext_ff->coeffs + offset-ilen, ilen+olen-1, tmp, ilen, ilen-1, ilen+olen-1, ctx);

        /* second scaling */
        for (slong j = 0; j < olen; j++)
        {
            fmpz_mod_mul(oval + j, G->ext_s2 + offset-ilen+j, oval + j, ctx);
            fmpz_mod_mul(oval + j, G->ext_s1f + offset+j, oval + j, ctx);
        }

        _fmpz_vec_clear(tmp, ilen);
    }

    /* backward extrapolation */
    else
    {
        const slong tlen = FLINT_MAX(ilen, olen);
        fmpz * tmp = _fmpz_vec_init(tlen);

        /* first scaling */
        for (slong i = 0; i < ilen; i++)
        {
            fmpz_mod_mul(tmp + i, G->ext_s2 + ilen-1-i, ival + ilen-1-i, ctx);
            fmpz_mod_mul(tmp + i, G->ext_s3 + i, tmp + i, ctx);
        }

        /* middle product */
        _fmpz_mod_poly_mulmid(oval, G->ext_fb->coeffs - (offset+olen), ilen+olen-1, tmp, ilen, ilen-1, ilen+olen-1, ctx);

        /* second scaling */
        for (slong j = 0; j < olen; j++)
            fmpz_set(tmp + j, oval + olen - 1 - j);
        for (slong j = 0; j < olen; j++)
        {
            fmpz_mod_mul(oval + j, G->ext_s3 + (-offset-1-j), tmp + j, ctx);
            fmpz_mod_mul(oval + j, G->ext_s1b + ilen-1-offset-j, oval + j, ctx);
        }

        _fmpz_vec_clear(tmp, tlen);
    }
}

void fmpz_mod_poly_extrapolate_geometric(fmpz * oval, slong olen,
                                         const fmpz * ival, slong ilen,
                                         slong offset, const fmpz_t r,
                                         const fmpz_mod_ctx_t ctx)
{
    if (olen == 0)
        return;

    if (ilen == 0)
    {
        _fmpz_vec_zero(oval, olen);
        return;
    }

    if (ilen == 1)
    {
        for (slong i = 0; i < olen; i++)
            fmpz_set(oval + i, ival);
        return;
    }

    fmpz_mod_geometric_progression_t G;
    slong len = (offset > 0) ? offset+olen : ilen-offset;
    _fmpz_mod_geometric_progression_init_function(G, r, len, UWORD(4), ctx);
    fmpz_mod_poly_extrapolate_geometric_precomp(oval, olen, ival, ilen, offset, G, ctx);
    fmpz_mod_geometric_progression_clear(G, ctx);
}
