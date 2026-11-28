# The (5,5,3) branch of the Beal conjecture

This is a formalization of part of Bjorn Poonen's published proof for the signature (5,5,3). It addresses the positive difference with multiplier 25. The corresponding [Left to Solve leaf](https://lefttosolve.com/p/BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H2.R1.H2) was obtained by Hennyrick's cofactor reduction. The full Beal conjecture concerns all triples of exponents greater than two.

## From the cofactor to the quartic

Write d = 25 s³ with s > 0. In Quartic.lean, model_iff proves that the natural-number equation

    5v⁴ + d(10v³ + 10v²d + 5vd² + d³) = 5t³

is equivalent, for these same v,s,t, to y³ = f(x) at x = v/s³ and y = t/s⁴, where

    f(x) = x⁴ + 50x³ + 1250x² + 15625x + 78125.

The map to the elliptic quotient has coordinates U = 4y/25 and V = (8x² + 200x + 2500)/125. The kernel checks that the quartic equation is equivalent to V² = U³ + 80 at these coordinates. The two possible abscissae giving the same V are x and −25−x. Every positive witness gives a point moved by this involution. The general characterization of rational points on the quartic requires a separate argument.

Source: B. Poonen, *Some Diophantine equations of the form xⁿ+yⁿ=zᵐ*, Acta Arithmetica 86 (1998), 193–205, section 4. [Journal and DOI](https://doi.org/10.4064/aa-86-3-193-205) · [Full paper](https://bibliotekanauki.pl/articles/1390678.pdf).

## Reproduce

Use Lean 4.33.1 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. In a Lake project with that dependency, copy both Lean files to the project root and run:

    lake env lean -DwarningAsError=true -o Quartic.olean Quartic.lean
    lake env bash -c 'export LEAN_PATH=".:$LEAN_PATH"; lean -DwarningAsError=true Audit.lean'

Audit.lean prints the axioms of each public theorem.
