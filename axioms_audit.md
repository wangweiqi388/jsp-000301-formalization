# Axiom audit — JSP-000301 Lean 4 formalization

Proof commit: `9e0e773dd0459f6ab56be14920522ef9fdc8ed03` (branch `main`).
Toolchain: Lean `v4.34.0` + Mathlib `v4.34.0`.

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

## How to reproduce this audit (run_print_axioms.sh)

The audit is fully reproducible with the bundled script [`run_print_axioms.sh`](run_print_axioms.sh):

```bash
git clone https://github.com/wangweiqi388/jsp-000301-formalization
cd jsp-000301-formalization && git checkout 9e0e773dd0459f6ab56be14920522ef9fdc8ed03
bash run_print_axioms.sh      # prints the axiom set and writes axioms_snippet.md
```

What the script does, transparently:

1. Appends the two `#print axioms` lines to a **temporary copy** of `jsp000301proof.lean`.
2. Runs a clean build (`lake build`, falling back to `lake env lean jsp000301proof.lean`).
3. Extracts each `'name' depends on axioms: [...]` line.
4. **Restores `jsp000301proof.lean` byte-for-byte** (a backup is made first and re-applied on exit,
   so the pinned proof source is unchanged — verified by checksum).

**Why a standalone `axioms_check.lean` is not used:** in this Lake layout a non-module file placed at
the repo root cannot resolve `import jsp000301proof` via `lake env lean` (it is not in the package's
module graph), so the append-and-restore approach above is the reliable way to surface `#print axioms`
for the package's root theorem. The pinned proof file is never modified permanently.

> Note on `Classical.choice`: although `by_cases hp23 : p = 23` and `by_cases hp2 : p = 2` are
> ℕ-equality cases (decidable), the overall elaboration of the proof draws on `Classical.choice`
> elsewhere, which is why the measured set is the standard triple. The `#print axioms` output above
> is the authoritative answer.
