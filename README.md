# Hilbert functions of chopped ideals of general plane points

Lean formalization of Theorem 1.1 and Corollary 5.1 of
[Hilbert Functions of Chopped Ideals of General Plane Points](Hilbert_functions_of_chopped_plane_point_ideals.pdf)
over arbitrary characteristic-zero fields. It proves the full Hilbert function, regular-sequence cases, least
stabilization degree, and the Expected Syzygy Conjecture.

The independent Mathlib-only statements are in
[Challenge.lean](Challenge.lean), with proofs in [Solution.lean](Solution.lean).

- Theorem 1.1: `ChoppedPlanePaper.main_result` (`ChoppedPlane.main_theorem`).
- Corollary 5.1: `ChoppedPlanePaper.expected_syzygy_result`
  (`ChoppedPlane.expected_syzygy_theorem`).

The project pins Lean `v4.35.0-rc3`, Mathlib commit
`8accc04827c389e678c3ef83e623b402e7480394`, and the dependency manifest.

```sh
./scripts/build-and-audit.sh
./scripts/verify-comparator.sh --native
```

For Linux verification with the bubblewrap sandbox, use
`./scripts/verify-comparator.sh` without `--native`.

Author and maintainer: Vlado Vojdanovski. AI-assisted development using OpenAI
Codex (GPT-6). Licensed under [Apache-2.0](LICENSE).
