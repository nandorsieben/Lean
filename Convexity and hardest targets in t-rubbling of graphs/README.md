# Lean certificates

for the article **Convexity and hardest targets in t-rubbling of graphs**.

## Verification

Requires Python 3.9 or later and [elan](https://github.com/leanprover/elan),
the Lean toolchain manager. Ensure `lean` is on your PATH. The file
`lean/lean-toolchain` pins Lean 4.35.0; elan installs that version when needed.
Only Lean's standard library is used. No Mathlib, Python packages, or external
rubbling solver is required.

From the repository root, run:

```sh
python3 lean/check.py
```

The checker rebuilds all 22 modules, treats warnings as errors, and audits the
49 printed axiom-dependency lists. A successful run ends with `PASS` and writes
`lean/.build/verification.log`. The only permitted proof axioms are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.

## Correspondence with the paper

All theorem names below are in the namespace `RubblingFamily`.
The hardest-target regime theorem additionally assumes `n >= 6` and
`m+n >= 3*floor(n/2)+2`.

| Paper result | Lean source | Theorem |
| --- | --- | --- |
| Lemma 3.1 | [Arithmetic.lean](lean/Arithmetic.lean) | `floor_le_iff`, `floor_three_bound` |
| Figures 3.2–3.3: move and parity changes | [ParityWeight.lean](lean/ParityWeight.lean) | `vi_pair_numeric`, `vi_strict_numeric`, `far1_add_one`, `far1_remove_one`, `far1_remove_two` |
| Proposition 3.2: four target thresholds | [Family.lean](lean/Family.lean) | `target_formula` |
| Corollary 3.3: graph threshold | [Family.lean](lean/Family.lean) | `family_number` |
| Note after Corollary 3.3: eventual linearity with slope four | [Family.lean](lean/Family.lean) | `family_eventually_linear` |
| Proposition 4.1: hardest-target regimes | [Consequences.lean](lean/Consequences.lean) | `hardest_target_regimes` |
| Example 5.1: hardest targets and empty intersection | [Consequences.lean](lean/Consequences.lean) | `graph_5_6_targets`, `graph_5_6_no_common_target` |
| Example 5.2: arbitrarily late target changes | [Consequences.lean](lean/Consequences.lean) | `arbitrarily_late_switch` |
| Example 5.3: first five values and nonconvexity/nonconcavity | [Consequences.lean](lean/Consequences.lean) | `graph_example_values`, `graph_nonconvex_nonconcave`, `graph_example_targets` |

[Rubbling.lean](lean/Rubbling.lean) defines the graph, distributions, legal moves,
reachability, and exact target thresholds. The graph-wide threshold and the
connection between its target values and hardest targets are in
[Family.lean](lean/Family.lean). The remaining modules prove the delivery,
weight, and arithmetic lemmas used by the main results. Some helper lemmas
hold over broader parameter ranges; the public formulas use the paper's range.

`Hρ m n t r` represents membership in the paper's set of hardest rubbling
targets. The intersection in Example 5.1 ranges over positive `t`.

The graph uses indices `0, ..., m+n-1`: the first `m` indices correspond to
`U_C` and `V_C`, and the remaining `n` to `U_I` and `V_I`. Relabeling these
indices gives the notation in the paper.
