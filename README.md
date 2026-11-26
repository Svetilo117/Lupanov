# Lupanov’s contact-circuit synthesis

This Lean 4 project formalizes Lupanov’s Theorem 8.1. For every Boolean function on $n$ variables, it constructs an undirected contact circuit and proves that its terminals are connected exactly on the inputs where the function is true.

For $n \ge 1024$, the circuit uses at most $\frac{2^n}{n}(1 + 200/\lfloor\sqrt n\rfloor)$ contacts. The main result is `Lupanov.theorem_8_1` in [Lupanov.lean](Lupanov.lean).

Run `lake build` from the project directory to check the proofs with Lean 4.24.0.
