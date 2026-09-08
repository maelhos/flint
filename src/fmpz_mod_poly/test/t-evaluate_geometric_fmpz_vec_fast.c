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

/* random prime with at least `minbits` bits, plus a random extra amount */
void _fmpz_mod_poly_test_geometric_randprime(fmpz_t p, flint_rand_t state,
                                             flint_bitcnt_t minbits)
{
    flint_bitcnt_t bits = FLINT_MAX(minbits, 3) + n_randint(state, 128);
    fmpz_randprime(p, state, bits, 0);
}

/* random r such that q = r**2 has multiplicative order at least `n` */
void _fmpz_mod_poly_test_geometric_randr(fmpz_t r, flint_rand_t state, slong n,
                                         const fmpz_mod_ctx_t ctx)
{
    fmpz_t q, t;

    fmpz_init(q);
    fmpz_init(t);

    while (1)
    {
        int ok = 1;

        fmpz_randm(r, state, fmpz_mod_ctx_modulus(ctx));
        if (fmpz_is_zero(r))
            continue;

        fmpz_mod_mul(q, r, r, ctx);
        fmpz_one(t);
        for (slong k = 1; k < n; k++)
        {
            fmpz_mod_mul(t, t, q, ctx);
            if (fmpz_is_one(t))
            {
                ok = 0;
                break;
            }
        }

        if (ok)
            break;
    }

    fmpz_clear(q);
    fmpz_clear(t);
}

TEST_FUNCTION_START(fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast, state)
{
    int i, result = 1;
    fmpz_mod_ctx_t ctx;
    fmpz_t p, r;

    fmpz_init(p);
    fmpz_init(r);
    fmpz_mod_ctx_init_ui(ctx, 2);

    for (i = 0; i < 100 * flint_test_multiplier(); i++)
    {
        fmpz_mod_poly_t P;
        fmpz * y, * z;
        slong n, npoints, nmax;

        npoints = (i < 10) ? i : n_randint(state, 100);
        n = n_randint(state, 150);
        nmax = FLINT_MAX(npoints, n);

        _fmpz_mod_poly_test_geometric_randprime(p, state, FLINT_BIT_COUNT(2*nmax + 2) + 1);
        fmpz_mod_ctx_set_modulus(ctx, p);
        _fmpz_mod_poly_test_geometric_randr(r, state, nmax, ctx);

        fmpz_mod_poly_init(P, ctx);
        y = _fmpz_vec_init(npoints);
        z = _fmpz_vec_init(npoints);

        fmpz_mod_poly_randtest(P, state, n, ctx);

        fmpz_mod_poly_evaluate_geometric_fmpz_vec_iter(y, P, r, npoints, ctx);
        fmpz_mod_poly_evaluate_geometric_fmpz_vec_fast(z, P, r, npoints, ctx);

        result = _fmpz_vec_equal(y, z, npoints);

        if (!result)
        {
            flint_printf("FAIL:\n");
            flint_printf("mod=%{fmpz}, r=%{fmpz}, n=%wd, npoints=%wd\n\n", p, r, n, npoints);
            flint_printf("P: "); fmpz_mod_poly_print_pretty(P, "x", ctx); flint_printf("\n\n");
            flint_printf("y: %{fmpz*}\n\n", y, npoints);
            flint_printf("z: %{fmpz*}\n\n", z, npoints);
            fflush(stdout);
            flint_abort();
        }

        fmpz_mod_poly_clear(P, ctx);
        _fmpz_vec_clear(y, npoints);
        _fmpz_vec_clear(z, npoints);
    }

    fmpz_clear(p);
    fmpz_clear(r);
    fmpz_mod_ctx_clear(ctx);

    TEST_FUNCTION_END(state);
}
