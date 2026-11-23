# Lean proofs

Files: Fl/H1.lean, Fl/H2.lean, Fl/H3.lean, Fl/AL.lean, Fl/AL001.lean, Fl/AL005.lean (namespace FL).
Statements used in the paper: sharp_drag (AL005, statement (5) with the sharp coefficient), al002_tight and al002_const (AL, the gamma-ratio bound with the first constant), al005 (AL005, the cubic floor).

## Pinned build
- Lean: leanprover/lean4:v4.37.0-rc1 (file lean-toolchain)
- Mathlib: tag v4.37.0-rc1, commit 31ce06eaadf4a200c0e1407c5f10953cf606b8f8 (file lake-manifest.json pins it and its dependencies)
- Rebuilt from scratch on 2026-11-23 on a Google Colab CPU session: "Build completed successfully (18302 jobs)", no sorry in the sources, and all 16 checked theorems depend only on the axioms propext, Classical.choice and Quot.sound. Full log: ../results/lean_pin_rebuild_2026-11-23.log (stage timings in ../results/lean_pin_rebuild_2026-11-23.json). The earlier build logs of 2026-11-22 are also in ../results/.

## Build it yourself
Install elan (the Lean version manager), then:

    cd lean
    lake exe cache get      # downloads prebuilt Mathlib files
    lake build Fl.H1 Fl.H2 Fl.H3 Fl.AL Fl.AL001 Fl.AL005

The files end with `#print axioms` lines, so the axiom report appears in the build output.

Lean checks the deduction from the stated assumptions. It does not check the data.
