open util/graph[Node] as graph
open util/ordering[State] as so

sig Node {e: set Node}
one sig Root extends Node {}

fact Graph {
	noSelfLoops[e]
	stronglyConnected[e] // no lose parts
}

sig State {
	// set of tree nodes in current state
	graph: set Node,
	// parent pointers in current state
	parent: Node -> Node
}

pred init {
	let fs = so/first | { fs.tree = Root and no fs.parent }
}

pred explore [pre, post: State] {
	some x,y : Node | x in pre.graph
				   and y in x.e
                        and y->x !in pre.parent
				   and post.parent = pre.parent + y->x
}

fact createTree {
	init
	all s: State - so/last |
	let s' = so/next[s] | extend[s,s']
}

pred solveShit[] {
	!some x,y:Node | x->y in last[].parent and y->x in last[].parent
}

run solveShit for 5 state
