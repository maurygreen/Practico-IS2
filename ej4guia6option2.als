open util/ordering[state]

// Puto el que lee
abstract sig Node {e: set Node}

one sig E0, E1, E2, E3, E4 extends Node {}

fact edges {
	e = E0 -> E1 + E1 -> E3 + E1 -> E4 + E0 -> E2 + E4 -> E0
}

sig state {
	graph: set Node,
	trans: Node -> Node
}

fact initialState {
	let s0 = first[] |
	    s0.graph = Node && no s0.trans 
}

pred explore[pre,post:state] {
	some x,y: Node | x in pre.graph
				and y in x.e
				and x->y !in pre.trans
				and post.trans = pre.trans + x->y
				//and x.e in x.(pre.trans + x->y) => post.graph = pre.graph - x
}

fact statetrans {
	all s: state, s':next[s] | explore[s,s']
}

//Esto es mentira, no es que el grafo sea aciclico
//pred solveshit[] {
//	all x,y: Node | x->y in last[].trans => y->x !in last[].trans
//}
//run solveshit for 6

pred show[] {}
run show for 6

assert Acyclic {
	all x,y: Node | x->y in last[].trans => x !in y.^(last[].trans)
}

check Acyclic
