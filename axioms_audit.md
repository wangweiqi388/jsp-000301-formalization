# Axiom audit — JSP-000301 Lean 4 formalization

Proof commit: `9e0e773dd0459f6ab56be14920522ef9fdc8ed03` (branch `main`).
Audit method: appended the two `#print axioms` commands to `jsp000301proof.lean` and ran a clean
build (`lake env lean jsp000301proof.lean`), Lean `v4.34.0` + Mathlib `v4.34.0`. The file was
restored afterwards; the pinned proof source is unchanged.

Standard Lean axioms are not disqualifying; the exact set is reported below, verbatim from the
actual command output.

## Command

```lean
#print axioms JSP000301.erdos_365_witness
#print axioms JSP000301.counterexample_family
```

## Output (actual)

```
'JSP000301.erdos_365_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP000301.counterexample_family' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Interpretation

Both target theorems depend only on the three **standard classical Lean axioms** — `propext`
(propositional extensionality), `Classical.choice` (the axiom of choice), and `Quot.sound`
(quotient soundness). These are the ordinary axioms used throughout Mathlib; they are **not**
disqualifying. There is **no** `sorry`, no `admit`, and no added unproved assumption.

> Note: although `by_cases hp23 : p = 23` and `by_cases hp2 : p = 2` are ℕ-equality cases
> (decidable), the overall elaboration of the proof still draws on `Classical.choice` elsewhere,
> which is why the measured axiom set is the standard triple. The `#print axioms` output above is
> the authoritative answer.
