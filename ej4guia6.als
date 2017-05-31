sig Nodo {}

sig Grafo {
	nodos: set Nodo,
	aristas: nodos -> nodos
}

pred aciclico[g:Grafo] {
	no (iden & ^(g.aristas)) 
}

pred reflexiva[g:Grafo] {
	~(g.aristas) in g.aristas
}

pred fconexo[g:Grafo] {
	g.nodos -> g.nodos = ^(g.aristas)
}

pred conexo[g:Grafo] {
	g.nodos -> g.nodos = ^(g.aristas) + ^(~(g.aristas))
}

run aciclico for 5 but 1 Grafo
run reflexiva for 5 but 1 Grafo
run fconexo for 5 but 1 Grafo
run conexo for 2 but 1 Grafo
