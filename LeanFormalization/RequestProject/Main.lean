import Mathlib
import RequestProject.Defs
import RequestProject.Lemma12
import RequestProject.Saturation
import RequestProject.RemoveEdge

namespace DoublySaturated

/-! # Main Theorem: The Circulant Graph is Doubly Saturated R(4, L)

We prove that for m ≥ 2 (equivalently L = m+2 ≥ 4), the circulant graph G_m
on 6m+1 vertices with connection set {m} ∪ [2m+1, 3m] is doubly saturated R(4, m+2).

The proof relies on four lemmas:
1. G_m is K₄-free (cliqueFree_four in Lemma12.lean)
2. G_m has no independent set of size m+2 (indepFree in Lemma12.lean)
3. Adding any non-edge creates K₄ (add_edge_creates_clique in Saturation.lean) ✓
4. Removing any edge creates I_{m+2} (remove_edge_creates_indep in RemoveEdge.lean)
-/

/-- The circulant graph G_m is doubly saturated R(4, m+2) for m ≥ 2. -/
theorem circulant_doubly_saturated (m : ℕ) (hm : m ≥ 2) :
    IsDoublySaturatedRST (G m) 4 (m + 2) := by
  refine ⟨⟨cliqueFree_four m hm, indepFree m hm⟩, ?_, ?_⟩
  · intro u v huv hnadj hrst
    exact add_edge_creates_clique m hm u v huv hnadj hrst.1
  · intro u v hadj hrst
    exact remove_edge_creates_indep m hm u v hadj hrst.2

/-- For L ≥ 4, the circulant graph G_{L-2} is doubly saturated R(4, L). -/
theorem circulant_doubly_saturated_R4L (L : ℕ) (hL : L ≥ 4) :
    IsDoublySaturatedRST (G (L - 2)) 4 L := by
  have hm : L - 2 ≥ 2 := by omega
  have hL' : L - 2 + 2 = L := by omega
  rw [← hL']
  exact circulant_doubly_saturated (L - 2) hm

end DoublySaturated
