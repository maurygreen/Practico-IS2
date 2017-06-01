sig Val {}

sig Relacion {
	vals: set Val,
	rel: vals -> vals
}

// ANTISIMETRIA
pred antisimetrica[r:Relacion] {
	(r.rel)&~(r.rel) in iden
}
// TRANSITIVIDAD
pred transitiva[r:Relacion] {
	(r.rel).(r.rel) in r.rel
}
// REFLEXIVA
pred reflexiva[r:Relacion]{
	(r.vals -> r.vals)&iden in r.rel
}
// ORDEN PARCIAL
pred ordenParcial[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	reflexiva[r]
}
// TOTALIDAD
pred totalidad[r:Relacion] {
	(r.vals-> r.vals) in r.rel + ~(r.rel)
}
// PREORDEN
pred preorden[r:Relacion] {
	reflexiva[r]
	and
	transitiva[r]
}
// ORDEN TOTAL
pred ordenTotal[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	reflexiva[r]
	and
	totalidad[r]
}
// ANTIREFLEXIVILIDAD
pred antireflexiva[r:Relacion] {
	(r.vals -> r.vals)&iden in ((r.vals -> r.vals) - r.rel)
}

// ORDEN ESTRICTO
pred ordenEstricto[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	antireflexiva[r]
}

// TIENE PRIMER ELEMENTO
pred tienePrimerElem[r:Relacion, x:Val] {
	ordenParcial[r] and
	all y:r.vals | x->y in r.rel
}

// TIENE ULTIMO ELEMENTO
pred tieneUltimoElem[r:Relacion, x:Val] {
	ordenParcial[r] and
	all y:r.vals | y->x in r.rel
}

run preorden for 5 but 1 Relacion
run ordenParcial for 5 but 1 Relacion
run ordenTotal for 5 but 1 Relacion
run ordenEstricto for 5 but 1 Relacion
run tienePrimerElem for 5 but 1 Relacion
run tieneUltimoElem for 5 but 1 Relacion

// ORDEN PARCIAL => ORDEN TOTAL
assert parcialistotal {
	all r:Relacion | ordenParcial[r] implies ordenTotal[r]
}

assert parcialprimelem {
	all r:Relacion | ordenParcial[r] implies (one x:Val | tienePrimerElem[r,x])
}

assert unionestricto {
	all r,r':Relacion | ordenEstricto[r] and ordenEstricto[r'] => ordenEstricto[r+r']
}

//assert compestricto {
//	all r,r':Relacion | ordenEstricto[r] and ordenEstricto[r'] => ordenEstricto[r.r']
//}

check parcialistotal
check unionestricto
check parcialprimelem
//check compestricto
