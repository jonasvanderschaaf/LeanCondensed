/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Category.LightProfinite.Basic

open CategoryTheory

universe u

def empty_subset {X : LightProfinite} (hX : IsEmpty X) (s : Set X) : s = ⊤ := by
  ext x
  exact hX.elim x

def empty_map {X Y : LightProfinite} (hY : IsEmpty Y) (f : X ⟶ Y) : IsEmpty X :=
  ⟨fun x ↦ hY.elim (f x)⟩

def empty_iso {X Y : LightProfinite} (hY : IsEmpty Y) (f : X ⟶ Y) : IsIso f := by
  let finv : Y ⟶ X := CompHausLike.ofHom _ {
    toFun y := hY.elim y
    continuous_toFun := by
      apply Continuous.mk
      intro s empty_elim
      rw [empty_subset hY ((fun y ↦ hY.elim y) ⁻¹' s)]
      exact TopologicalSpace.isOpen_univ }
  refine IsIso.mk ⟨finv, ?_⟩
  constructor <;> ext x
  exact hY.elim (f x)
  exact hY.elim x
