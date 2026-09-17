# External kernel check (con-leche)

This repo is a Lean 4 / Mathlib slice of Zhi-Wei Sun, *Catalan's constant is
irrational* (arXiv:2609.04176v1). `lake build` is the ordinary check: Lean’s
C++ kernel accepted the default target. We also run
[con-leche](https://github.com/leanprover/con-leche) on every push.

## What con-leche is

An **external Lean kernel**, written in Lean, with its own terms (not
`Lean.Expr`). It does not read `.lean` files. The pipeline is:

```text
lake build
lean4export CatalanSun > catalan-sun.ndjson   # toolchain tag = lean-toolchain
con-leche --verified catalan-sun.ndjson
```

`--verified` is the mode the consistency proof is about. If `checkDecls`
accepts a stream, the resulting environment has a `Model` in their set-theory
interface: ZF **without Infinity**, plus an **ω-chain of Grothendieck
universes**; Choice is taken from Lean as the meta-logic (not from the object
theory). In that model `False` is empty and `Eq` is set equality, so **no
accepted proof of `False`**.

That statement is **parametric** in `[SetTheory V]`. CI does not build such a
`V` and does not prove ZFC. It is the same extra assumption as Lean’s usual
consistency story (Carneiro: ZFC + ω inaccessibles). A separate con-leche
bridge package shows Carneiro’s hypothesis implies their interface; this repo
does not run that bridge.

Exit codes: **0** accept, **1** reject (invalid environment), **2** decline
(feature the checker does not support yet), **3** error / OOM. CI fails on
anything but 0.

Pins live in `.github/workflows/con-leche.yml` (`CON_LECHE_REV`,
`LEAN4EXPORT_REF`). Bump them on purpose, not by floating `master`.

## Why we run it

`lake build` and con-leche are different programs. A bug only in the official
kernel would have to be reproduced here to still accept a bad proof. The
checker also **rejects a used `sorry`** and **extra axioms** (the three
standard ones — `propext`, `Classical.choice`, `Quot.sound` — are allowed).

It is **not** a replacement for `lake build`, and it does **not** add
mathematical content (no new lemma about *G*).

## What the runs show for this formalization

Measured on GitHub `ubuntu-latest`, commit `8663999`,
[Actions run 2](https://github.com/chokmah-me/catalan-sun-lean/actions/runs/35216050384):

- export: **39 068 387** NDJSON lines (CatalanSun **plus** the Mathlib /
  Batteries / … cone `lean4export` walks from the default target);
- `con-leche: accepted 362547 declarations (--verified)` in ~9.5 min
  (job ~13.5 min).

So the **currently proved** default-target material — Theorem 2.1, absolute
Corollary 2.1, det-level Lemma 5.4, Theorem 5.1, Lemma 5.5’s (5.2), and the
supporting lemmas — is, after export, a kernel environment this checker
accepts. If the set-theory hypothesis holds, those statements are true in the
model (they are not a proof of `False`).

**Not shown:**

- Theorem 1.1 (*G* irrational) — still open here;
- Lemma 5.5 (5.3), Corollary 5.2, Props 6.3/7.4, Mertens/PNT — not on the
  accepted stream as proved claims if they are not in the library yet;
- “ZFC proved Catalan's constant is irrational”;
- a full Mathlib audit (only this library’s dependency cone);
- independence from the Lean compiler that *built* the con-leche binary.

Later pushes re-export and re-check. A red job means the new commit is not
accepted in this sense, not that the paper is refuted.
