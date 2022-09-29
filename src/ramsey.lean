import .basic
import combinatorics.pigeonhole

namespace simple_graph
open finset
universes u v w

variables {V : Type u}

open_locale classical

structure edge_coloring (G : simple_graph V) (α : Type w):=
(f : sym2 V → α)

-- first we want to prove that K_3 is subgraph of K_6
def complete_le_subgraph_complete (n k : ℕ) (h : k ≤ n) :
  (complete_graph (fin k)) ↪g (complete_graph (fin n)) :=
{ to_fun := sorry,
  inj' := sorry,
  map_rel_iff' := sorry }

variables (α : Type w) (colors : edge_coloring (⊤ : simple_graph (fin 6)) (fin 2))


-- grab arbitrary vertex and use pigeonhole to say it has at least 3 red or 3 blue edges
lemma edge_red_or_blue (v : fin 6) :
  ∃ y : (fin 2), 3 ≤ (((⊤ : simple_graph (fin 6)).incidence_finset v).filter
  $ λ e, colors.f e = y).card :=
begin
  sorry,
end

end simple_graph
