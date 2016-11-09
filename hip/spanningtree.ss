data node{
int val;
node left;
node right
}

relation update(abstract G, node x, int d, abstract G1).
relation lookup(abstract G, node x, int d, node l, node r).

relation span(abstract G, node x, abstract G1).
relation subset_reach(abstract G, node x, abstract G1).
relation eq_notreach(abstract G, node x, abstract G1).

graph<G> == self = null
       or self::node<v,l,r> U* (l::graph<G> U* r::graph<G>)
	     & lookup(G,self,v,l,r);

rlemma "graph_gen_left_null" x::node<v1,l1,r> * (x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      	& lookup(G,x,v,l,r) & update(G,x,v1,G1)
     -> x::node<v1,l1,r> U* (l1::graph<G1> U* r::graph<G1>) & l1 = null;

rlemma "graph_gen_right_null" x::node<v1,l,r1> * (x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      	& lookup(G,x,v,l,r) & update(G,x,v1,G1)
     -> x::node<v1,l,r1> U* (l1::graph<G1> U* r1::graph<G1>) & r1 = null;

rlemma "pttoupdate" x::node<v1,l,r> * (x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & lookup(G,x,v,l,r) & update(G,x,v1,G1)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma "subgraphupdate_l" l::graph<G1> * (l::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & subset_reach(G,l,G1) & eq_notreach(G,l,G1) & lookup(G,x,v,l,r) & lookup(G1,x,v1,l,r)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma "subgraphupdate_r" r::graph<G1> * (r::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & subset_reach(G,r,G1) & eq_notreach(G,r,G1) & lookup(G,x,v,l,r) & lookup(G1,x,v1,l,r)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

axiom lookup(G,x,0,_,_) ==> x != null.

axiom true ==> span(G,null,G).

axiom lookup(G,x,1,_,_) ==> span(G,x,G).

axiom span(G,x,G1) & lookup(G,y,v,l,r) ==> subset_reach(G,x,G1) & eq_notreach(G,x,G1) & lookup(G1,y,_,l,r).

axiom lookup(G,x,v,l,r) & update(G,x,1,G1) & v != 1 & span(G1,l,G2) & span(G2,r,G3) ==> span(G,x,G3) & lookup(G3,x,1,l,r).

void spanning(node x)
requires x::graph<G> & lookup(G,x,0,_,_)
ensures x::graph<G1> & span(G,x,G1);
{
  node l,r;
  l = x.left;
  r = x.right;
  x.val = 1;
  if(l != null) {
    if(l.val == 0)
      spanning(l);
    else x.left = null;
  }
  if(r != null) {
    if(r.val == 0)
      spanning(r);
    else x.right = null;
  }
}