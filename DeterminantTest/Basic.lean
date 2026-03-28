import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open Finset Matrix BigOperators

noncomputable section
namespace DeterminantTest

/-- A point in the Euclidean plane (ℝ²). -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite set of points in the Euclidean plane. -/
abbrev PointSet := Finset Point

/-- A set of points is in *general position* if it contains
    no collinear triples and no concyclic quadruples. -/
def GeneralPosition (S : PointSet) : Prop :=
  (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      p ≠ q → q ≠ r → p ≠ r →
      ¬ Collinear ℝ {p, q, r}) ∧
  (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S,
      p ≠ q → p ≠ r → p ≠ s →
      q ≠ r → q ≠ s → r ≠ s →
      ¬ EuclideanGeometry.Concyclic {p, q, r, s})

/-- Determinant criterion for collinearity of three points in ℝ². -/
def collinearDet (p q r : Point) : ℝ :=
  let m : Matrix (Fin 3) (Fin 3) ℝ :=
    ![
      ![p 0, p 1, 1],
      ![q 0, q 1, 1],
      ![r 0, r 1, 1]
    ]
  m.det

/-- Three points are collinear iff the determinant of their collinearMatrix is zero. -/
lemma collinear_iff_det_zero (p q r : Point) :
  Collinear ℝ ({p, q, r} : Set Point) ↔ collinearDet p q r = 0 := by
  constructor <;> intro h
  · unfold DeterminantTest.collinearDet
    rw [collinear_iff_exists_forall_eq_smul_vadd] at h
    simp_all [Matrix.det_fin_three]
    rcases h with ⟨ base_pt, dir_vec, ⟨ t_p, rfl ⟩, ⟨ t_q, rfl ⟩, ⟨ t_r, rfl ⟩ ⟩
    norm_num
    ring
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    use p
    unfold DeterminantTest.collinearDet at h
    simp only [Matrix.det_fin_three] at h
    simp only [Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      Matrix.cons_val, mul_one, one_mul] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, vadd_eq_add, forall_eq_or_imp,
      right_eq_add, smul_eq_zero, exists_or_eq_left, forall_eq, true_and]
    by_cases h_qx_eq_px : q 0 = p 0
    · by_cases h_qy_eq_py : q 1 = p 1
      · have h_p_eq_q : p = q := by ext i; fin_cases i <;> simp [h_qx_eq_px, h_qy_eq_py]
        subst h_p_eq_q
        use r - p
        constructor <;> [use 0; use 1]
        · simp only [zero_smul, zero_add]
        · simp only [one_smul, sub_add_cancel]
      · use !₂[0, 1]
        constructor
        · use q 1 - p 1
          ext i; fin_cases i <;> simp [h_qx_eq_px]
        · use r 1 - p 1
          ext i; fin_cases i
          · have h_det_factorized : (p 0 - r 0) * (q 1 - p 1) = 0 := by
              rw [h_qx_eq_px] at h; rw [← h]; ring
            rcases eq_zero_or_eq_zero_of_mul_eq_zero h_det_factorized
              with h_rx_eq_px | h_qy_eq_py_contradiction
            · rw [sub_eq_zero] at h_rx_eq_px; simp [h_rx_eq_px]
            · rw [sub_eq_zero] at h_qy_eq_py_contradiction; contradiction
          · simp
    · use q - p
      constructor
      · use 1; simp
      · use (r 0 - p 0) / (q 0 - p 0)
        ext i; fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue,
            PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [div_mul_cancel₀]
          · ring
          · exact sub_ne_zero.mpr h_qx_eq_px
        · simp; field_simp [sub_ne_zero.mpr h_qx_eq_px]; nlinarith [h]

/-- Construct a 4×4 matrix to detect concyclicity of points in ℝ². -/
def cocyclicDet (p q r s : Point) : ℝ :=
  let m : Matrix (Fin 4) (Fin 4) ℝ :=
    ![
      ![p 0, p 1, ‖p‖^2, 1],
      ![q 0, q 1, ‖q‖^2, 1],
      ![r 0, r 1, ‖r‖^2, 1],
      ![s 0, s 1, ‖s‖^2, 1]
    ]
  m.det

/-- Four points are concyclic iff the determinant of their cocyclicMatrix is zero. -/
lemma cocyclic_iff_det_zero (p q r s : Point) (not_collinear : ¬ Collinear ℝ {p, q, r}):
  EuclideanGeometry.Concyclic {p, q, r, s} ↔ cocyclicDet p q r s = 0 := by
  sorry

end DeterminantTest

#lint
