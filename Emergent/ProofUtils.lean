import Mathlib.Analysis.SpecialFunctions.Exp
import Emergent.Logic
import Emergent.Physics

namespace ProofUtils

open RecursiveSelf

theorem not_coherent_of_collapsed (t : ℝ) : Collapsed t → ¬Coherent t := by
  intro h hC; unfold Collapsed Coherent ψself at *; exact h hC.left

theorem Secho_pos (t : ℝ) (_ : ψself t) : Secho t > 0 :=
  Real.exp_pos (-1.0 / (t + 1.0))

end ProofUtils
