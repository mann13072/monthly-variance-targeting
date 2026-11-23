# Lean proofs

Files: H1.lean, H2.lean, H3.lean, AL.lean, AL001.lean, AL005.lean (namespace FL). Statements used in the paper: sharp_drag (AL005, statement (5) with the sharp coefficient), al002_tight and al002_const (AL, the gamma-ratio bound with the first constant), al005 (AL005, the cubic floor). The build logs in ../results/*_final_build.log show Lean 4.37.0-rc1, "Build completed successfully", no sorry, and axioms propext, Classical.choice, Quot.sound only.

## How the files were built (Colab, 2026-11-22)
    lake +leanprover-community/mathlib4:lean-toolchain new fl math
    mkdir -p fl/Fl && cp *.lean fl/Fl/
    cd fl && lake exe cache get && lake build Fl.H1 Fl.H2 Fl.H3 Fl.AL Fl.AL001 Fl.AL005

**Known gap:** the project's lakefile, lean-toolchain and lake-manifest.json were not saved, so the exact Mathlib commit is not recorded (the project followed Mathlib's toolchain current on 2026-11-22). Before publishing, rebuild once and commit the generated lake-manifest.json so the proofs are pinned.
