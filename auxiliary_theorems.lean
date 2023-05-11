/-
    Tasnia Kader
    May 10th, 2023
-/

import data.real.basic
import data.finset.fin
import analysis.matrix
import data.matrix.notation
import data.matrix.basic

open_locale matrix

lemma inj (n : ℕ) : function.injective (matrix.to_lin (pi_Lp.basis_fun 2 ℝ (fin n)) (pi_Lp.basis_fun 2 ℝ (fin n))) :=
by exact equiv_like.injective (matrix.to_lin (pi_Lp.basis_fun 2 ℝ (fin n)) (pi_Lp.basis_fun 2 ℝ (fin n)))

lemma matrix_transpose (α : Type){a₁₁ a₁₂ a₂₁ a₂₂ : α} : 
!![a₁₁, a₁₂; a₂₁, a₂₂]ᵀ = !![a₁₁, a₂₁; a₁₂, a₂₂] :=
by {ext i j, fin_cases i; fin_cases j; simp [matrix.transpose_apply]}

@[simp] lemma matrix_one : (!![1, 0; 0, 1] : matrix (fin 2) (fin 2) ℝ) = 1 := 
by {ext i j, fin_cases i; fin_cases j; simp [matrix.one_apply]} 

noncomputable def ref_x_rot (θ : ℝ) : matrix (fin 2) (fin 2) ℝ := 
!![-real.cos (θ), real.sin (θ); real.sin (θ), real.cos (θ)]

noncomputable def reflect_2D (θ : ℝ) : matrix (fin 2) (fin 2) ℝ := 
!![real.cos (2 * θ), real.sin (2 * θ); real.sin (2 * θ), - real.cos (2 * θ)] 

noncomputable def rotation_2D (θ : ℝ) : matrix (fin 2) (fin 2) ℝ := 
!![real.cos θ, - real.sin θ; real.sin θ, real.cos θ] 

noncomputable def rotoreflection_2D (θ φ : ℝ) : matrix (fin 2) (fin 2) ℝ := 
rotation_2D (θ) ⬝ reflect_2D (φ)

noncomputable def reflrotation_2D (θ φ : ℝ) : matrix (fin 2) (fin 2) ℝ := 
reflect_2D (φ) ⬝ rotation_2D (θ)
