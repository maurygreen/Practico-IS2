sig Nodo {}

sig Grafo {
	nodos: set Nodo,
	aristas: nodos -> nodos
}

pred reflexiva[g:Grafo] {
	~(g.aristas) in g.aristas
}

pred aciclico[g:Grafo] {
	no (iden & ^(g.aristas)) 
}

pred arbol[g:Grafo] {
	aciclico[g] and
	all x,y: g.nodos | x -> y in g.aristas implies !(some z: g.nodos - x | z -> y in g.aristas)
	
}

run conexo for 5 but 1 Grafo
run 	arbol for 5 but 1 Grafo
