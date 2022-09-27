import data.rel
import data.set.finite
import data.sym.sym2
import set_theory.cardinal.finite
import algebra.big_operators.finprod

open_locale classical big_operators

noncomputable theory

open finset
universes u v w

variables {V : Type u} {E : Type v}

structure graph (V : Type u) (E : Type v) :=
(ends : E → sym2 V)

namespace graph

section basic

variables {G : graph V E} {u v : V} {e f : E}

def adj (G : graph V E) : V → V → Prop :=
  λ v w, ∃ (e : E), G.ends e = ⟦(v, w)⟧

def inc (G : graph V E) : V → E → Prop :=
  λ v e, v ∈ G.ends e

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidence_set (G : graph V E) (v : V) : set E := {e : E | v ∈ G.ends e}

/-- Make a graph from the digraph -/
def graph.mk {V : Type u} {E : Type v} (ends : E → sym2 V) : graph V E := { ends := ends }

@[symm] lemma adj_symm (h : G.adj u v) : G.adj v u :=
begin
  sorry,
end

/-!
A dart is an edge with a chosen orientation - graphs are naturally unoriented,
but in order to talk about things like walks, the handshaking lemma, etc you have to
pick a "direction" to traverse the edges.
-/
structure dart (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(e : E)
(h : G.ends e = ⟦(head, tail)⟧)

/-!
Flipping a dart around
-/
def reverse_dart (G : graph V E) (d : G.dart) : G.dart :=
{ head := d.tail,
  tail := d.head,
  e := d.e,
  h :=
    begin
      sorry,
    end }

@[simp]
lemma reverse_head_tail (G : graph V E) (d : G.dart) : (G.reverse_dart d).tail = d.head :=
begin
  sorry,
end

@[simp]
lemma reverse_tail_head (G : graph V E) (d : G.dart) : (G.reverse_dart d).head = d.tail :=
begin
  sorry,
end

end basic

section walks

variables (G : graph V E)
/-!
We have a very clever definition of walks here that one of my colleagues at Waterloo
came up with. One of the issues we had when talk about walks was, when we'd try to talk
about them in an inductive way, we'd end up missing the start or end vertex. This definition
includes both in a neat way.
-/
structure walk (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(darts : list G.dart)
(is_walk :
  [head] ++ (list.map dart.tail darts)
  = (list.map dart.head darts) ++ [tail])

lemma walk_rev_head (p : walk G) :
  list.map dart.head (list.map G.reverse_dart p.darts) =
    (list.map dart.tail p.darts) :=
begin
  sorry,
end

lemma walk_rev_tail (p : walk G) :
  list.map dart.tail (list.map G.reverse_dart p.darts) =
    (list.map dart.head p.darts) :=
begin
  sorry,
end

/-!
Having seen how to write some definitions, try writing the definition of
the empty walk! Hint: By our definition, we do need a start and end vertex, so
we have to use arbitrary vertex v.
-/
def empty_walk (v : V) : walk G :=
{ head := sorry,
  tail := sorry,
  darts := sorry,
  is_walk := sorry }

/-!
The reverse of a walk p.
-/
def reverse (p : walk G) : walk G :=
{ head := sorry,
  tail := sorry,
  darts := (list.map G.reverse_dart p.darts.reverse),
  -- including the above because you probably haven't seen lists in lean yet (?)
  is_walk :=
    begin
      sorry,
    end }

/-!
Appending two walks p and q, where the tail of p is the head of q.
-/
def append (p q : walk G) (h : p.tail = q.head) : walk G :=
{ head := sorry,
  tail := sorry,
  darts := p.darts ++ q.darts,
  is_walk :=
    begin
      sorry,
    end }

/-!
We have reachable as a definition here so that we can start talking about connectivity.
You'll find that the previous definitions of various walks are useful in showing that
reachability is an equivalence relation:
-/
def reachable (u v : V) : Prop := ∃ (p : G.walk), p.head = u ∧ p.tail = v

namespace walk

/-!
Reachability is reflexive, i.e. a vertex can reach itself
-/
@[refl] protected lemma reachable.refl (u : V) : G.reachable u u :=
begin
  sorry,
end
protected lemma reachable.rfl {u : V} : G.reachable u u := reachable.refl _ _

/-!
If you have a walk from u to v, you have a walk from v to u
-/
@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
begin
  sorry,
end

/-!
If you have a walk from u to v and a walk from v to w, then you have a walk from
u to w
-/
@[trans] protected lemma reachable.trans {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w)
  : G.reachable u w :=
begin
  sorry,
end

def edges {G : graph V E} (p : G.walk) : list E := list.map dart.e p.darts

def support {G : graph V E} (p : G.walk) : list V := [p.head] ++ list.map dart.head p.darts

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {G : graph V E} (p : G.walk) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A *path* is a walk with no repeating vertices. -/
structure is_path {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.nodup)

/-- A *circuit* is a nonempty trail beginning and ending at the same vertex. -/
-- extends path & need to get rid of loops
structure is_circuit {G : graph V E} (p : G.walk) : Prop :=
(start_end : p.head = p.tail)
(ne_nil : p.darts ≠ [])

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.tail.nodup)

end walk

end walks

section conn

def connected (G : graph V E) : Prop := ∀ u v : V, G.reachable u v

def is_loop_edge_of (G : graph V E) (v : V) (e : E) : Prop := G.ends e = sym2.diag v

def is_loop_edge (G : graph V E) (e : E) : Prop := sym2.is_diag (G.ends e)

def degree (G : graph V E) (v : V) : ℕ := nat.card (G.incidence_set v)
  + nat.card {e | G.is_loop_edge_of v e}
-- double count loop edges

/-!
This is a harder problem so don't sweat it - honestly I haven't even proven this
version of the handshaking lemma yet! We do have the handshaking lemma in lean,
it just has a different appearance due to different definitions.
-/
theorem handshake (G : graph V E) [fintype V] [fintype E] :
  ∑ᶠ (x : V), G.degree x = 2 * (fintype.card E) :=
begin
  sorry,
end

/-!
From here I'm including some more of the things that I'm thinking about with graphic matroids -
it's not complete and there aren't really lemmas here to be completed, I just thought it would maybe
be instructive to see what we have to do with subgraphs.
-/

def regular (G : graph V E) (k : ℕ) : Prop := ∀ (v : V), G.degree v = k

lemma is_trail_def {G : graph V E} (p : G.walk) : p.is_trail ↔ p.edges.nodup :=
⟨walk.is_trail.edges_nodup, λ h, ⟨h⟩⟩


structure subgraph (G : graph V E) :=
(verts : set V)
(edges : set E)
(edge_sub : ∀ (e : edges), (G.ends e).to_set ⊆ verts)

end conn

namespace subgraph

variables (G : graph V E)

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

def ends (G' : subgraph G) (e : E) (h : e ∈ G'.edges) : sym2 (G'.verts) :=
begin
  refine ⟦(G'.vert _ (quotient.out (G.ends e)).1 _, G'.vert _ (quotient.out (G.ends e)).2 _)⟧,
  exact set.mem_of_subset_of_mem (G'.edge_sub ⟨e, h⟩) (sym2.to_set_mem1 (G.ends e)),
  exact set.mem_of_subset_of_mem (G'.edge_sub ⟨e, h⟩) (sym2.to_set_mem2 (G.ends e)),
end
-- coercion between "ends" in subgraph to graph?
-- probably easier to do with "e.other" but whatever

def adj (G' : subgraph G) : G'.verts → G'.verts → Prop :=
  λ v w, ∃ (e ∈ G'.edges), G'.ends G e H = ⟦(v, w)⟧

protected def coe {G : graph V E} (G' : subgraph G) : graph G'.verts G'.edges :=
{ ends := λ e, G'.ends G e e.2 }





end subgraph
end graph
