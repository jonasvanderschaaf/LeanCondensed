/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.CategoryTheory.Countable

universe u

noncomputable section

open CategoryTheory Quiver Countable

instance {J : Type u} [Countable J] [Category J] [IsThin J] :
    CountableCategory J :=
  CountableCategory.mk inferInstance inferInstance

noncomputable instance {J : Type u} [Finite J] [Category J] [IsThin J] : FinCategory J := by
  apply FinCategory.mk (Fintype.ofFinite _) (fun j j' ↦ Fintype.ofFinite _)
