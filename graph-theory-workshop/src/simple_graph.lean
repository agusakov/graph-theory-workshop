import combinatorics.simple_graph

open finset
universes u v w

namespace simple_graph
variables {𝕜 : Type*} {V : Type u} {W : Type v} {X : Type w} (G : simple_graph V)
  (G' : simple_graph W) {a b c u v w : V} {e : sym2 V}
/-!

# Intro to Graph Theory

If you're familiar with graph theory, you may have already noticed that we've narrowed down to
a specific definition of a graph that actually doesn't encompass everything that graph theory
has to offer. For the scope of this project (unless someone suggests otherwise, of course!)
we'll be focusing on *simple* graphs - they're graphs with properties that make them nice to work
with. 

Traditionally, the definition of a simple graph is a vertex type V and edge type E such that
* no vertex has an edge to itself (irreflexive)
* for every pair of vertices u, v ∈ V, if u has an edge to v, v has an edge to u (symmetric)
* no two vertices can have more than one edge between them 

So the way we've defined this in Lean is a bit different. Instead of having an explicit edge type,
we have an adjacency relation between pairs of vertices that says either they're adjacent or they're
not. The definition looks like this:
```
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(symm : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)
```

Let's prove some simple lemmas about it!
-/

-- If u is adjacent to v, then v is adjacent to u
lemma adj_symm' (h : G.adj u v) : G.adj v u := 
begin
  sorry,
end

-- If two vertices are adjacent, then they're not equal
lemma ne_of_adj' (h : G.adj a b) : a ≠ b :=
begin
  sorry,
end

/-!
See if you can complete the definitions of the complete graph and the empty graph!
-/

def complete_graph' (V : Type u) : simple_graph V := { 
  adj := ne, -- `ne` is "not equal", so the relation is that a pair of vertices
              -- is adjacent if they're not equal
  symm := 
    begin
      sorry,
    end
  loopless :=
    begin
      sorry,
    end }

def empty_graph' (V : Type u) : simple_graph V := { 
  adj := λ i j, false, -- in other words, for every pair of vertices, adjacency between them is "false"
  symm := 
    begin
      sorry,
    end
  loopless :=
    begin
      sorry,
    end }

/-!
You'll notice that we don't actually define a simple graph as having a distinct edge type. 
Rather, we've made the edges implicit in the definition by saying we have an adjacency relation
between the vertices, and then the edge type emerges from that as a set of unordered pairs of
vertices that are related, like so:
```
def edge_set : set (sym2 V) := sym2.from_rel G.symm
```

Tricky problem: See if you can prove that two vertices are adjacent if and only if there is a 
corresponding element in the edge set of G! (Hint: I've included some helper lemmas!)
-/

lemma adj_iff_exists_edge' {v w : V} :
  G.adj v w ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  sorry,
end

/-!
Now we're gonna look at some basic definitions we need to talk about properties of graphs.

```
def neighbor_set (v : V) : set V := set_of (G.adj v)
```
-/

lemma mem_neighbor_set' (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
begin
  sorry,
end

/-!
```
def incidence_set (v : V) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}
```
-/

lemma incidence_set_subset' (v : V) : G.incidence_set v ⊆ G.edge_set :=
begin
  sorry,
end

lemma mk_mem_incidence_set_left_iff' : ⟦(a, b)⟧ ∈ G.incidence_set a ↔ G.adj a b :=
begin
  sorry,
end

lemma mk_mem_incidence_set_right_iff' : ⟦(a, b)⟧ ∈ G.incidence_set b ↔ G.adj a b :=
begin
  sorry,
end

lemma mem_incidence_set' (v w : V) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj v w :=
begin
  sorry,
end

lemma mem_incidence_iff_neighbor' {v w : V} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
begin
  sorry,
end