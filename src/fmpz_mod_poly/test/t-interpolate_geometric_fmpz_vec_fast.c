/*
    Copyright (C) 2026, Vincent Neiger, Éric Schost
    Copyright (C) 2026, Mael Hostettler

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

TEST_FUNCTION_START(fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast, state)
{
    int i, result = 1;
    fmpz_mod_ctx_t ctx;
    fmpz_t p, r;

    fmpz_init(p);
    fmpz_init(r);
    fmpz_mod_ctx_init_ui(ctx, 2);

    for (i = 0; i < 200 * flint_test_multiplier(); i++)
    {
        fmpz_mod_poly_t P, Q;
        fmpz * y;
        slong len, npoints;

        npoints = 1 + n_randint(state, 100);
        len = 1 + n_randint(state, npoints);

        _fmpz_mod_poly_test_geometric_randprime(p, state, FLINT_BIT_COUNT(2*npoints + 2) + 1);
        fmpz_mod_ctx_set_modulus(ctx, p);
        _fmpz_mod_poly_test_geometric_randr(r, state, npoints, ctx);

        y = _fmpz_vec_init(npoints);

        /* use full `npoints` points */
        {
            fmpz_mod_poly_init(P, ctx);
            fmpz_mod_poly_init(Q, ctx);
            fmpz_mod_poly_randtest(P, state, len, ctx);

            fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(y, P, r, npoints, ctx);
            fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast(Q, r, y, npoints, ctx);
            result = fmpz_mod_poly_equal(P, Q, ctx);
            if (!result)
            {
                flint_printf("FAIL (all points):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, len=%wd, npoints=%wd\n\n", p, r, len, npoints);
                fmpz_mod_poly_print_pretty(P, "x", ctx), flint_printf("\n\n");
                fmpz_mod_poly_print_pretty(Q, "x", ctx), flint_printf("\n\n");
                fflush(stdout);
                flint_abort();
            }

            fmpz_mod_poly_clear(P, ctx);
            fmpz_mod_poly_clear(Q, ctx);
        }

        /* use only `len` points */
        {
            fmpz_mod_poly_init(P, ctx);
            fmpz_mod_poly_init(Q, ctx);
            fmpz_mod_poly_randtest(P, state, len, ctx);

            fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(y, P, r, npoints, ctx);
            fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast(Q, r, y, len, ctx);
            result = fmpz_mod_poly_equal(P, Q, ctx);
            if (!result)
            {
                flint_printf("FAIL (`len` points):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, len=%wd, npoints=%wd\n\n", p, r, len, npoints);
                fmpz_mod_poly_print_pretty(P, "x", ctx), flint_printf("\n\n");
                fmpz_mod_poly_print_pretty(Q, "x", ctx), flint_printf("\n\n");
                fflush(stdout);
                flint_abort();
            }

            fmpz_mod_poly_clear(P, ctx);
            fmpz_mod_poly_clear(Q, ctx);
        }

        /* use only `len` points, interpolate then evaluate */
        {
            fmpz * val = _fmpz_vec_init(len);

            fmpz_mod_poly_init(P, ctx);
            for (slong k = 0; k < len; k++)
                fmpz_randm(y + k, state, p);

            fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast(P, r, y, len, ctx);
            fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(val, P, r, len, ctx);
            result = _fmpz_vec_equal(val, y, len);
            if (!result)
            {
                flint_printf("FAIL (`len` points, interpolate then evaluate):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, len=%wd, npoints=%wd\n\n", p, r, len, npoints);
                flint_printf("val = %{fmpz*}\n", val, len);
                flint_printf("y = %{fmpz*}\n", y, len);
                fflush(stdout);
                flint_abort();
            }

            _fmpz_vec_clear(val, len);
            fmpz_mod_poly_clear(P, ctx);
        }

        /* use variant with given precomputation */
        {
            fmpz_mod_geometric_progression_t G;

            fmpz_mod_geometric_progression_init(G, r, npoints, ctx);
            fmpz_mod_poly_init(P, ctx);
            fmpz_mod_poly_init(Q, ctx);
            fmpz_mod_poly_randtest(P, state, len, ctx);

            _fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast_precomp(y, P->coeffs, P->length, G, npoints, ctx);
            fmpz_mod_poly_fit_length(Q, len, ctx);
            _fmpz_mod_poly_interpolate_geometric_fmpz_vec_fast_precomp(Q->coeffs, y, G, len, ctx);
            _fmpz_mod_poly_set_length(Q, len);
            _fmpz_mod_poly_normalise(Q);
            result = fmpz_mod_poly_equal(P, Q, ctx);
            if (!result)
            {
                flint_printf("FAIL (precomp):\n");
                flint_printf("mod=%{fmpz}, r=%{fmpz}, len=%wd, npoints=%wd\n\n", p, r, len, npoints);
                fmpz_mod_poly_print_pretty(P, "x", ctx), flint_printf("\n\n");
                fmpz_mod_poly_print_pretty(Q, "x", ctx), flint_printf("\n\n");
                fflush(stdout);
                flint_abort();
            }

            fmpz_mod_poly_clear(P, ctx);
            fmpz_mod_poly_clear(Q, ctx);
            fmpz_mod_geometric_progression_clear(G, ctx);
        }

        _fmpz_vec_clear(y, npoints);
    }

    fmpz_clear(p);
    fmpz_clear(r);
    fmpz_mod_ctx_clear(ctx);

    TEST_FUNCTION_END(state);
}
