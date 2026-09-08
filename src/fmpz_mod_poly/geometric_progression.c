/*
    Copyright (C) 2026, Vincent Neiger, Éric Schost, Mael Hostettler
    Copyright (C) 2026, Vincent Neiger
    Copyright (C) 2026, Maël Hostettler

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

static
void _fmpz_mod_geometric_progression_evaluate_init(fmpz_mod_geometric_progression_t G,
                                                   const fmpz_t r, slong len,
                                                   const fmpz_t q, const fmpz_t inv_r,
                                                   const fmpz_t inv_q,
                                                   const fmpz_mod_ctx_t ctx)
{
    /* G->ev_f = sum_{0 <= i < 2*len - 1} q**(i*i/2) * x**i */
    /* G->ev_s[i] = 1 / q**(i*i/2)                          */
    fmpz_t rr, ir;

    fmpz_mod_poly_init2(G->ev_f, 2*len - 1, ctx);
    G->ev_s = _fmpz_vec_init(len);

    _fmpz_mod_poly_set_length(G->ev_f, 2*len - 1);

    fmpz_init_set(rr, r);
    fmpz_init_set(ir, inv_r);

    fmpz_one(G->ev_f->coeffs);
    for (slong i = 1; i < 2*len - 1; i++)
    {
        fmpz_mod_mul(G->ev_f->coeffs + i, G->ev_f->coeffs + i - 1, rr, ctx);
        fmpz_mod_mul(rr, rr, q, ctx);  /* r**(2*i+1) */
    }

    fmpz_one(G->ev_s);
    for (slong i = 1; i < len; i++)
    {
        fmpz_mod_mul(G->ev_s + i, G->ev_s + i - 1, ir, ctx);
        fmpz_mod_mul(ir, ir, inv_q, ctx);
    }

    fmpz_clear(rr);
    fmpz_clear(ir);
}

static
void _fmpz_mod_geometric_progression_interpolate_init(fmpz_mod_geometric_progression_t G,
                                                      slong len,
                                                      const fmpz_t q, const fmpz_t inv_q,
                                                      const fmpz_mod_ctx_t ctx)
{
    /* quantities for Newton interpolation/evaluation/change-of-basis */
    /* see [Bostan - Schost, J.Complexity 2005, Section 5.1]          */
    /* write u_i for prod_{1 <= k <= i} (q**k - 1),                   */
    /*   and q_i for q**(i*(i-1)/2)                                   */

    /* coeff(G->int_f, i) = (-1)**i * q_i / u_i */
    fmpz_t q_pow_i, inv_q_pow_i, inv_q_i, prod_diff;

    fmpz_mod_poly_init2(G->int_f, len, ctx);
    _fmpz_mod_poly_set_length(G->int_f, len);

    /* G->int_s1[i] = 1 / u_i */
    /* G->int_s2[i] = u_i / q_i */
    G->int_s1 = _fmpz_vec_init(len);
    G->int_s2 = _fmpz_vec_init(len);

    fmpz_one(G->int_f->coeffs);
    fmpz_one(G->int_s2);

    fmpz_init_set_ui(q_pow_i, 1);
    fmpz_init_set_ui(inv_q_pow_i, 1);
    fmpz_init_set_ui(inv_q_i, 1);
    fmpz_init_set_ui(prod_diff, 1);

    for (slong i = 1; i < len; i++)
    {
        fmpz_mod_mul(inv_q_i, inv_q_i, inv_q_pow_i, ctx);        /* 1 / q_i */
        fmpz_mod_mul(inv_q_pow_i, inv_q_pow_i, inv_q, ctx);      /* 1 / q**i */
        fmpz_mod_mul(G->int_f->coeffs + i, G->int_f->coeffs + i - 1, q_pow_i, ctx);  /* q_i */
        fmpz_mod_mul(q_pow_i, q_pow_i, q, ctx);                  /* q**i */
        fmpz_mod_sub_ui(G->int_s1 + i - 1, q_pow_i, 1, ctx);     /* temporarily, q**i - 1 */
        fmpz_mod_mul(prod_diff, G->int_s1 + i - 1, prod_diff, ctx);  /* u_i */
        fmpz_mod_mul(G->int_s2 + i, prod_diff, inv_q_i, ctx);    /* u_i / q_i */
    }

    fmpz_mod_inv(G->int_s1 + len - 1, prod_diff, ctx);  /* 1 / u_{len-1} */
    for (slong i = len - 1; i > 0; i--)
    {
        /* G->int_s1 + i is 1 / u_i */
        fmpz_mod_mul(G->int_f->coeffs + i, G->int_f->coeffs + i, G->int_s1 + i, ctx);
        if (i % 2)  /* i odd, - q_i / u_i */
            fmpz_mod_neg(G->int_f->coeffs + i, G->int_f->coeffs + i, ctx);
        fmpz_mod_mul(G->int_s1 + i - 1, G->int_s1 + i - 1, G->int_s1 + i, ctx);  /* 1 / u_{i-1} */
    }

    fmpz_clear(q_pow_i);
    fmpz_clear(inv_q_pow_i);
    fmpz_clear(inv_q_i);
    fmpz_clear(prod_diff);
}

static
void _fmpz_mod_geometric_progression_extrapolate_init(fmpz_mod_geometric_progression_t G,
                                                      slong len,
                                                      const fmpz_t q, const fmpz_t inv_q,
                                                      const fmpz_mod_ctx_t ctx)
{
    /* ext_ff: sum_{i=0}^{len-1} x**i / (q**(i+1) - 1)    [for forward]  */
    /* ext_fb: sum_{i=0}^{len-1} x**i / (q**(-i-1) - 1)   [for backward] */
    fmpz_t q_pow_i, inv_q_pow_i;

    fmpz_mod_poly_init2(G->ext_ff, len - 1, ctx);
    fmpz_mod_poly_init2(G->ext_fb, len - 1, ctx);
    _fmpz_mod_poly_set_length(G->ext_ff, len - 1);
    _fmpz_mod_poly_set_length(G->ext_fb, len - 1);

    /* ext_s1f[i] = prod_{k=1}^{i} (q**k - 1)    [for forward]  */
    /* ext_s1b[i] = prod_{k=1}^{i} (q**(-k) - 1) [for backward] */
    /* ext_s2[i] = 1 / ext_s1f[i]                [for both]     */
    /* ext_s3[i] = 1 / ext_s1b[i]                [for both]     */
    G->ext_s1f = _fmpz_vec_init(len);
    G->ext_s1b = _fmpz_vec_init(len);
    G->ext_s2 = _fmpz_vec_init(len);
    G->ext_s3 = _fmpz_vec_init(len);

    fmpz_one(G->ext_s1f);
    fmpz_one(G->ext_s1b);

    fmpz_init_set(q_pow_i, q);
    fmpz_init_set(inv_q_pow_i, inv_q);

    for (slong i = 1; i < len; i++)
    {
        fmpz_mod_sub_ui(G->ext_ff->coeffs + i - 1, q_pow_i, 1, ctx);      /* temporarily, q**i - 1 */
        fmpz_mod_sub_ui(G->ext_fb->coeffs + i - 1, inv_q_pow_i, 1, ctx);  /* temporarily, q**(-i) - 1 */
        fmpz_mod_mul(G->ext_s1f + i, G->ext_s1f + i - 1, G->ext_ff->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->ext_s1b + i, G->ext_s1b + i - 1, G->ext_fb->coeffs + i - 1, ctx);
        fmpz_mod_mul(q_pow_i, q_pow_i, q, ctx);
        fmpz_mod_mul(inv_q_pow_i, inv_q_pow_i, inv_q, ctx);
    }

    fmpz_mod_inv(G->ext_s2 + len - 1, G->ext_s1f + len - 1, ctx);
    fmpz_mod_inv(G->ext_s3 + len - 1, G->ext_s1b + len - 1, ctx);

    for (slong i = len - 1; i > 0; i--)
    {
        fmpz_mod_mul(G->ext_s2 + i - 1, G->ext_s2 + i, G->ext_ff->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->ext_s3 + i - 1, G->ext_s3 + i, G->ext_fb->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->ext_ff->coeffs + i - 1, G->ext_s2 + i, G->ext_s1f + i - 1, ctx);
        fmpz_mod_mul(G->ext_fb->coeffs + i - 1, G->ext_s3 + i, G->ext_s1b + i - 1, ctx);
    }

    fmpz_clear(q_pow_i);
    fmpz_clear(inv_q_pow_i);
}

static
void _fmpz_mod_geometric_progression_interpolate_extrapolate_init(fmpz_mod_geometric_progression_t G,
                                                                  slong len,
                                                                  const fmpz_t q, const fmpz_t inv_q,
                                                                  const fmpz_mod_ctx_t ctx)
{
    /* ext_ff: sum_{i=0}^{len-1} x**i / (q**(i+1) - 1)    [for forward]  */
    /* ext_fb: sum_{i=0}^{len-1} x**i / (q**(-i-1) - 1)   [for backward] */
    fmpz_t q_pow_i, inv_q_pow_i, t;

    fmpz_mod_poly_init2(G->ext_ff, len - 1, ctx);
    fmpz_mod_poly_init2(G->ext_fb, len - 1, ctx);
    _fmpz_mod_poly_set_length(G->ext_ff, len - 1);
    _fmpz_mod_poly_set_length(G->ext_fb, len - 1);

    /* ext_s1f[i] = prod_{k=1}^{i} (q**k - 1)    [for forward]  */
    /* ext_s1b[i] = prod_{k=1}^{i} (q**(-k) - 1) [for backward] */
    /* ext_s2[i] = 1 / ext_s1f[i]                [for both]     */
    /* ext_s3[i] = 1 / ext_s1b[i]                [for both]     */
    G->ext_s1f = _fmpz_vec_init(len);
    G->ext_s1b = _fmpz_vec_init(len);
    G->ext_s2 = _fmpz_vec_init(len);
    G->ext_s3 = _fmpz_vec_init(len);

    /* coeff(G->int_f, i)  = (-1)**i * q**(i*(i-1)/2) / (prod_{k=1}^{i} (q**k - 1)) */
    /*                    == (-1)**i * q**(i*(i-1)/2) * ext_s2[i] */
    fmpz_mod_poly_init2(G->int_f, len, ctx);
    _fmpz_mod_poly_set_length(G->int_f, len);

    /* G->int_s1[i] = ext_s2[i] */
    /* G->int_s2[i] = ext_s1f[i] / q**(i*(i-1)/2) */
    G->int_s1 = G->ext_s2;
    G->int_s2 = _fmpz_vec_init(len);

    fmpz_one(G->ext_s1f);
    fmpz_one(G->ext_s1b);
    fmpz_one(G->int_f->coeffs);
    fmpz_one(G->int_s2);

    fmpz_init_set_ui(q_pow_i, 1);
    fmpz_init_set_ui(inv_q_pow_i, 1);
    fmpz_init(t);

    for (slong i = 1; i < len; i++)
    {
        fmpz_mod_neg(t, q_pow_i, ctx);
        /* temporarily, (-1)**i * q**(i*(i-1)/2) */
        fmpz_mod_mul(G->int_f->coeffs + i, G->int_f->coeffs + i - 1, t, ctx);
        /* temporarily, 1 / q**(i*(i-1)/2) */
        fmpz_mod_mul(G->int_s2 + i, G->int_s2 + i - 1, inv_q_pow_i, ctx);
        /* int_s2[i-1] is now ok */
        fmpz_mod_mul(G->int_s2 + i - 1, G->int_s2 + i - 1, G->ext_s1f + i - 1, ctx);
        fmpz_mod_mul(q_pow_i, q_pow_i, q, ctx);
        fmpz_mod_mul(inv_q_pow_i, inv_q_pow_i, inv_q, ctx);
        fmpz_mod_sub_ui(G->ext_ff->coeffs + i - 1, q_pow_i, 1, ctx);      /* temporarily, q**i - 1 */
        fmpz_mod_sub_ui(G->ext_fb->coeffs + i - 1, inv_q_pow_i, 1, ctx);  /* temporarily, q**(-i) - 1 */
        fmpz_mod_mul(G->ext_s1f + i, G->ext_s1f + i - 1, G->ext_ff->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->ext_s1b + i, G->ext_s1b + i - 1, G->ext_fb->coeffs + i - 1, ctx);
    }

    /* int_s2[len-1] is now ok */
    fmpz_mod_mul(G->int_s2 + len - 1, G->int_s2 + len - 1, G->ext_s1f + len - 1, ctx);
    fmpz_mod_inv(G->ext_s2 + len - 1, G->ext_s1f + len - 1, ctx);
    fmpz_mod_inv(G->ext_s3 + len - 1, G->ext_s1b + len - 1, ctx);

    for (slong i = len - 1; i > 0; i--)
    {
        fmpz_mod_mul(G->ext_s2 + i - 1, G->ext_s2 + i, G->ext_ff->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->int_f->coeffs + i, G->ext_s2 + i, G->int_f->coeffs + i, ctx);
        fmpz_mod_mul(G->ext_s3 + i - 1, G->ext_s3 + i, G->ext_fb->coeffs + i - 1, ctx);
        fmpz_mod_mul(G->ext_ff->coeffs + i - 1, G->ext_s2 + i, G->ext_s1f + i - 1, ctx);
        fmpz_mod_mul(G->ext_fb->coeffs + i - 1, G->ext_s3 + i, G->ext_s1b + i - 1, ctx);
    }

    fmpz_clear(q_pow_i);
    fmpz_clear(inv_q_pow_i);
    fmpz_clear(t);
}

/* initialize for selection of functionalities:                        */
/*    the lowest 3 bits of `function` act as a mask for the            */
/*    three functionalities, in this order:                            */
/*    evaluate(bit0)+interpolate(bit1)+extrapolate(bit2)               */
void _fmpz_mod_geometric_progression_init_function(fmpz_mod_geometric_progression_t G,
                                                   const fmpz_t r, slong len,
                                                   ulong function,
                                                   const fmpz_mod_ctx_t ctx)
{
    fmpz_t q, inv_r, inv_q;

    G->len = len;
    G->function = function;

    fmpz_init(q);
    fmpz_init(inv_r);
    fmpz_init(inv_q);

    fmpz_mod_mul(q, r, r, ctx);
    fmpz_mod_inv(inv_r, r, ctx);
    fmpz_mod_mul(inv_q, inv_r, inv_r, ctx);

    if (function & UWORD(1))  /* evaluate */
        _fmpz_mod_geometric_progression_evaluate_init(G, r, len, q, inv_r, inv_q, ctx);

    if ((function & UWORD(6)) == UWORD(6))  /* interpolate+extrapolate */
        _fmpz_mod_geometric_progression_interpolate_extrapolate_init(G, len, q, inv_q, ctx);
    else if ((function & UWORD(2)) == UWORD(2))  /* interpolate */
        _fmpz_mod_geometric_progression_interpolate_init(G, len, q, inv_q, ctx);
    else if ((function & UWORD(4)) == UWORD(4))  /* extrapolate */
        _fmpz_mod_geometric_progression_extrapolate_init(G, len, q, inv_q, ctx);

    fmpz_clear(q);
    fmpz_clear(inv_r);
    fmpz_clear(inv_q);
}

/* clear for selection of functionalities (see init)  */
static
void _fmpz_mod_geometric_progression_clear_function(fmpz_mod_geometric_progression_t G,
                                                    ulong function,
                                                    const fmpz_mod_ctx_t ctx)
{
    const slong len = G->len;

    if (function & UWORD(1))  /* evaluate */
    {
        _fmpz_vec_clear(G->ev_s, len);
        fmpz_mod_poly_clear(G->ev_f, ctx);
    }
    if ((function & UWORD(6)) == UWORD(6))  /* interpolate+extrapolate */
    {
        /* G->int_s1 is ext_s2: no alloc -> not cleared */
        _fmpz_vec_clear(G->int_s2, len);
        fmpz_mod_poly_clear(G->int_f, ctx);
        _fmpz_vec_clear(G->ext_s1f, len);
        _fmpz_vec_clear(G->ext_s1b, len);
        _fmpz_vec_clear(G->ext_s2, len);
        _fmpz_vec_clear(G->ext_s3, len);
        fmpz_mod_poly_clear(G->ext_ff, ctx);
        fmpz_mod_poly_clear(G->ext_fb, ctx);
    }
    else if ((function & UWORD(2)) == UWORD(2))  /* interpolate */
    {
        _fmpz_vec_clear(G->int_s1, len);
        _fmpz_vec_clear(G->int_s2, len);
        fmpz_mod_poly_clear(G->int_f, ctx);
    }
    else if ((function & UWORD(4)) == UWORD(4))  /* extrapolate */
    {
        _fmpz_vec_clear(G->ext_s1f, len);
        _fmpz_vec_clear(G->ext_s1b, len);
        _fmpz_vec_clear(G->ext_s2, len);
        _fmpz_vec_clear(G->ext_s3, len);
        fmpz_mod_poly_clear(G->ext_ff, ctx);
        fmpz_mod_poly_clear(G->ext_fb, ctx);
    }
}

/* initialize for all: evaluate+interpolate+extrapolate */
void fmpz_mod_geometric_progression_init(fmpz_mod_geometric_progression_t G,
                                         const fmpz_t r, slong len,
                                         const fmpz_mod_ctx_t ctx)
{
    _fmpz_mod_geometric_progression_init_function(G, r, len, UWORD(7), ctx);
}

/* clear for all: evaluate+interpolate+extrapolate */
void fmpz_mod_geometric_progression_clear(fmpz_mod_geometric_progression_t G,
                                          const fmpz_mod_ctx_t ctx)
{
    _fmpz_mod_geometric_progression_clear_function(G, G->function, ctx);
}
