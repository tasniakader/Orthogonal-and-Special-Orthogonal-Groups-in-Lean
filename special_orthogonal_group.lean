/-  
    Tasnia Kader
    May 10th, 2023
  
    ## Special Orthogonal Group

    ## References

    * [Anne Baanen, *special_linear_group*][baanen2020]
    * https://en.wikipedia.org/wiki/Orthogonal_group
-/

import data.real.basic
import auxiliary_theorems
import data.finsupp.fintype
import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse
import analysis.normed.group.basic
import analysis.inner_product_space.basic
import data.matrix.notation
import analysis.matrix
import orthogonal_group

namespace special_orthogonal_matrix
universes u v
variables (m : Type u)(α : Type v)
variables [decidable_eq m][fintype m][field α]

open_locale matrix
open orthogonal_matrix

instance has_coe_to_matrix : has_coe (orthogonal m α) (matrix m m α) :=
⟨λ A, A.val⟩

local prefix `↑ₘ`:1024 := @coe (orthogonal m α) (matrix m m α) _

section

def special_orth := {A : orthogonal m α // (↑ₘA).det = 1}

end

localized "notation `SO(` m `,` α `)`:= special_orthogonal_matrix.special_orth (fin m) α" in special_orthogonal_matrix

namespace special_orth

-- Instances

instance has_coe_to_orthogonal : has_coe (special_orth m α) (orthogonal m α) :=
⟨λ A, A.val⟩

local prefix `↑ₒ`:1024 := @coe _ (orthogonal m α) _

lemma special_orth_ext_iff (A B : special_orth m α) : A = B ↔ (∀ i j, ↑ₘ↑ₒA i j = ↑ₘ↑ₒB i j) := 
by rw [subtype.ext_iff, orthogonal.ext_iff]

instance has_one : has_one (special_orth m α) :=
⟨⟨1, by rw [orthogonal.coe_one, matrix.det_one]⟩⟩

instance has_inv : has_inv (special_orth m α) :=
⟨λ A, ⟨(↑ₒA)⁻¹, by rw [orthogonal.inv_coe, matrix.det_transpose, A.prop]⟩⟩

instance has_mul : has_mul (special_orth m α) :=
⟨λ A B, ⟨↑ₒA * ↑ₒB, by simp [B.prop, A.prop]⟩⟩

instance has_pow : has_pow (special_orth m α) ℕ :=
⟨λ A n, ⟨(↑ₒA) ^ n, by simp [A.prop]⟩⟩ 

instance : inhabited (special_orth m α) := ⟨1⟩

section coe_lemmas

variables (A B : special_orth m α)

@[simp] lemma coe_mk (A : orthogonal m α) (h : (↑ₘA).det = 1) :
  ↑ₒ(⟨A, h⟩ : special_orth m α) = A := rfl

@[simp] lemma inv_coe : ↑ₒ(A⁻¹) = (↑ₒA)⁻¹ := rfl

@[simp] lemma coe_mul : ↑ₒ(A * B) = ↑ₒA * ↑ₒB := rfl

@[simp] lemma coe_one : ↑ₒ(1 : special_orth m α) = (1 : orthogonal m α) := rfl

@[simp] lemma det_coe : (↑ₘ↑ₒA).det = 1 := A.prop

@[simp] lemma coe_pow (n : ℕ) : ↑ₒ(A ^ n) = (↑ₒA) ^ n := rfl

lemma coe_inv : (↑ₘ↑ₒA)⁻¹ = (↑ₘ↑ₒA)ᵀ := by simp

@[simp] lemma coe_inv_eq_inv_coe : (↑ₘ↑ₒA)⁻¹ = ↑ₘ↑ₒ(A⁻¹) := by simp

end coe_lemmas

-- Special Orthogonal Group Form a Group Under Matrix Multiplication

instance special_orth_monoid : monoid (special_orth m α) :=
{
  one_mul := λ A, by {ext, simp},
  mul_one := λ A, by {ext, simp},
  mul_assoc := λ A B C, by {ext, simp, rw matrix.mul_assoc},
  ..special_orth.has_mul _ _,
  ..special_orth.has_one _ _,
}

instance special_orth_group : group (special_orth m α) :=
{
  mul_left_inv := λ A, by {ext, simp},
  ..special_orth.special_orth_monoid _ _,
  ..special_orth.has_inv _ _,
}

-- Linear Transformation with an Associated Special Orthogonal Matrix

def to_lin' : special_orth m α →* (m → α) ≃ₗ[α] (m → α) :=
{
  to_fun := λ A,
  begin 
    have h₀ := linear_equiv.of_linear (matrix.to_lin' ↑ₘ↑ₒA) (matrix.to_lin' ↑ₘ↑ₒ(A⁻¹)),
    apply h₀,
    rw [← matrix.to_lin'_mul, ← coe_inv_eq_inv_coe, coe_inv, (↑ₒA).prop, matrix.to_lin'_one],
    rw [← matrix.to_lin'_mul, ← coe_inv_eq_inv_coe, coe_inv, orthogonal.orth_prop m α (↑ₒA), 
    matrix.to_lin'_one],
  end,
  map_one' := by {simp, exact rfl},
  map_mul' := λ A B, 
  begin 
    simp only [matrix.to_lin'_mul, mul_inv_rev, coe_mul, inv_coe, 
    orthogonal.coe_mul, orthogonal.inv_coe],
    exact rfl,
  end,
}

lemma to_lin'_apply (A : special_orth m α) (u : m → α) :
  special_orth.to_lin' m α A u = matrix.to_lin' ↑ₘ↑ₒA u := rfl

lemma to_lin'_symm_apply (A : special_orth m α) (u : m → α) :
  (special_orth.to_lin' m α A).symm u = matrix.to_lin' ↑ₘ↑ₒ(A⁻¹) u := rfl

lemma to_lin'_symm_to_linear_map (A : special_orth m α) :
  ↑((special_orth.to_lin' m α A).symm) = matrix.to_lin' ↑ₘ↑ₒ(A⁻¹) := rfl

def special_orth_to_GL : special_orth m α →* linear_map.general_linear_group α (m → α) := 
begin
  have h₀ := (linear_map.general_linear_group.general_linear_equiv α (m → α)).symm,
  have h₁ := special_orth.to_lin' m α,
  have h₂ := mul_equiv.to_monoid_hom h₀,
  apply monoid_hom.comp h₂ h₁,
end

-- Example of Elements in the Special Orthogonal Group

open examples

noncomputable def rotation_special_orth (θ : ℝ) : SO(2, ℝ) := ⟨rotation_2D_orth θ, 
begin 
  dsimp [rotation_2D_orth, rotation_2D], 
  simp only [matrix.det_fin_two_of, neg_mul, sub_neg_eq_add], 
  ring_nf, 
  simp,
end⟩

end special_orth

end special_orthogonal_matrix

namespace properties

open inner_product_geometry
open orthogonal_matrix.orthogonal
open_locale orthogonal_matrix
open_locale special_orthogonal_matrix

variables (n : ℕ)(A : SO(n, ℝ))
variables (u v : euclidean_space ℝ (fin n))

local prefix `↑ₒ`:1024 := @coe (SO(n, ℝ)) (O(n, ℝ)) _
local prefix `↑ₘ`:1024 := @coe (O(n, ℝ)) (matrix (fin n) (fin n) (ℝ)) _

local notation `⟪`x`, `y`⟫ₑ` := euclidean_space.inner_product_space.inner x y
local notation `T ` := matrix.to_euclidean_lin (↑ₘ↑ₒA)

theorem special_orth_presv_inner_prod : ⟪T u, T v⟫ₑ = ⟪u, v⟫ₑ :=
by {apply orth_presv_inner}

lemma special_orth_presv_norm : ‖ T u ‖ = ‖ u ‖ := 
by {apply orth_presv_norm}

lemma special_orth_presv_dist : dist (T u) (T v) = dist u v :=
by {apply orth_presv_dist}

lemma special_orth_is_iso : isometry ( T ) :=
by {apply orth_is_iso}

theorem special_orth_presv_angle : angle u v = angle (T u) (T v) :=
by {apply orth_presv_angle}

end properties