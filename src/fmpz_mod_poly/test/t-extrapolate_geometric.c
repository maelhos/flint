/*
    Copyright (C) 2026 Vincent Neiger, Kevin Tran
    Copyright (C) 2026 Maël Hostettler

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 3 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include "test_helpers.h"
#include "fmpz.h"
#include "fmpz_vec.h"
#include "fmpz_mod.h"
#include "fmpz_mod_poly.h"

/* defined in t-evaluate_geometric_fmpz_vec_fast.c */
void _fmpz_mod_poly_test_geometric_randprime(fmpz_t p, flint_rand_t state,
                                             flint_bitcnt_t minbits);
void _fmpz_mod_poly_test_geometric_randr(fmpz_t r, flint_rand_t state, slong n,
                                         const fmpz_mod_ctx_t ctx);

TEST_FUNCTION_START(fmpz_mod_poly_extrapolate_geometric, state)
{
    int i, result = 1;
    fmpz_mod_ctx_t ctx;
    fmpz_t p, r, q, c;

    fmpz_init(p);
    fmpz_init(r);
    fmpz_init(q);
    fmpz_init(c);
    fmpz_mod_ctx_init_ui(ctx, 2);

    for (i = 0; i < 50 * flint_test_multiplier(); i++)
    {
        fmpz_mod_poly_t P;
        fmpz * ival, * oval, * val;
        fmpz * ipts, * opts;
        slong ilen, olen, istart, offset, nmax;

        ilen = (i < 10) ? i : n_randint(state, 60);
        olen = (i < 10) ? i : n_randint(state, 60);

        ival = _fmpz_vec_init(ilen);
        oval = _fmpz_vec_init(olen);
        val = _fmpz_vec_init(olen);
        ipts = _fmpz_vec_init(ilen);
        opts = _fmpz_vec_init(olen);

        /* forward: offset >= ilen */
        {
            istart = n_randint(state, 50);
            offset = ilen + n_randint(state, 10);
            nmax = istart + offset + ilen + olen + 2;

            _fmpz_mod_poly_test_geometric_randprime(p, state, FLINT_BIT_COUNT(2*nmax + 2) + 1);
            fmpz_mod_ctx_set_modulus(ctx, p);
            _fmpz_mod_poly_test_geometric_randr(r, state, nmax, ctx);
            fmpz_mod_mul(q, r, r, ctx);

            fmpz_mod_poly_init(P, ctx);
            fmpz_mod_poly_randtest(P, state, ilen, ctx);

            do
            {
                fmpz_randm(c, state, p);
            } while (fmpz_is_zero(c));

            /* input points are c * q**k, k = istart...istart+ilen-1 */
            if (ilen > 0)
            {
                fmpz_mod_pow_ui(ipts, q, istart, ctx);
                fmpz_mod_mul(ipts, ipts, c, ctx);
                for (slong k = 1; k < ilen; k++)
                    fmpz_mod_mul(ipts + k, ipts + k - 1, q, ctx);
            }

            /* output points are c * q**k, k = istart+offset...istart+offset+olen-1 */
            if (olen > 0)
            {
                fmpz_mod_pow_ui(opts, q, istart + offset, ctx);
                fmpz_mod_mul(opts, opts, c, ctx);
                for (slong k = 1; k < olen; k++)
                    fmpz_mod_mul(opts + k, opts + k - 1, q, ctx);
            }

            fmpz_mod_poly_evaluate_fmpz_vec(ival, P, ipts, ilen, ctx);
            fmpz_mod_poly_evaluate_fmpz_vec(val, P, opts, olen, ctx);

            fmpz_mod_poly_extrapolate_geometric(oval, olen, ival, ilen, offset, r, ctx);

            result = _fmpz_vec_equal(oval, val, olen);

            if (!result)
            {
                flint_printf("FAIL (forward):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, ilen=%wd, olen=%wd, ", p, r, ilen, olen);
                flint_printf("istart=%wd, offset=%wd\n\n", istart, offset);
                flint_printf("ival: %{fmpz*}\n\n", ival, ilen);
                flint_printf("oval: %{fmpz*}\n\n", oval, olen);
                flint_printf("correct: %{fmpz*}\n\n", val, olen);
                fflush(stdout);
                flint_abort();
            }

            fmpz_mod_poly_clear(P, ctx);
        }

        /* backward: offset + olen <= 0 */
        {
            /* here we build the points explicitly, so we also need istart+offset >= 0 */
            istart = olen + 10 + n_randint(state, 50);
            offset = - (olen + (slong) n_randint(state, 10));
            nmax = istart + ilen + olen + 2;

            _fmpz_mod_poly_test_geometric_randprime(p, state, FLINT_BIT_COUNT(2*nmax + 2) + 1);
            fmpz_mod_ctx_set_modulus(ctx, p);
            _fmpz_mod_poly_test_geometric_randr(r, state, nmax, ctx);
            fmpz_mod_mul(q, r, r, ctx);

            fmpz_mod_poly_init(P, ctx);
            fmpz_mod_poly_randtest(P, state, ilen, ctx);

            do
            {
                fmpz_randm(c, state, p);
            } while (fmpz_is_zero(c));

            /* input points are c * q**k, k = istart...istart+ilen-1 */
            if (ilen > 0)
            {
                fmpz_mod_pow_ui(ipts, q, istart, ctx);
                fmpz_mod_mul(ipts, ipts, c, ctx);
                for (slong k = 1; k < ilen; k++)
                    fmpz_mod_mul(ipts + k, ipts + k - 1, q, ctx);
            }

            /* output points are c * q**k, k = istart+offset...istart+offset+olen-1 */
            if (olen > 0)
            {
                fmpz_mod_pow_ui(opts, q, istart + offset, ctx);
                fmpz_mod_mul(opts, opts, c, ctx);
                for (slong k = 1; k < olen; k++)
                    fmpz_mod_mul(opts + k, opts + k - 1, q, ctx);
            }

            fmpz_mod_poly_evaluate_fmpz_vec(ival, P, ipts, ilen, ctx);
            fmpz_mod_poly_evaluate_fmpz_vec(val, P, opts, olen, ctx);

            fmpz_mod_poly_extrapolate_geometric(oval, olen, ival, ilen, offset, r, ctx);

            result = _fmpz_vec_equal(oval, val, olen);

            if (!result)
            {
                flint_printf("FAIL (backward):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, ilen=%wd, olen=%wd, ", p, r, ilen, olen);
                flint_printf("istart=%wd, offset=%wd\n\n", istart, offset);
                flint_printf("ival: %{fmpz*}\n\n", ival, ilen);
                flint_printf("oval: %{fmpz*}\n\n", oval, olen);
                flint_printf("correct: %{fmpz*}\n\n", val, olen);
                fflush(stdout);
                flint_abort();
            }

            fmpz_mod_poly_clear(P, ctx);
        }

        _fmpz_vec_clear(ival, ilen);
        _fmpz_vec_clear(oval, olen);
        _fmpz_vec_clear(val, olen);
        _fmpz_vec_clear(ipts, ilen);
        _fmpz_vec_clear(opts, olen);
    }

    fmpz_clear(p);
    fmpz_clear(r);
    fmpz_clear(q);
    fmpz_clear(c);
    fmpz_mod_ctx_clear(ctx);

    TEST_FUNCTION_END(state);
}
