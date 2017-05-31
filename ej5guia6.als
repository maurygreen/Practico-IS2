sig Val {}

sig Relacion {
	vals: set Val,
	rel: vals -> vals
}

pred antisimetrica[r:Relacion] {
	(r.rel)&~(r.rel) in iden
}

pred transitiva[r:Relacion] {
	(r.rel).(r.rel) in r.rel
}

pred reflexiva[r:Relacion]{
	(r.vals -> r.vals)&iden in r.rel
}

pred ordenParcial[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	reflexiva[r]
}

pred totalidad[r:Relacion] {
	(r.vals-> r.vals) in r.rel + ~(r.rel)
}

pred preorden[r:Relacion] {
	reflexiva[r]
	and
	transitiva[r]
}

pred ordenTotal[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	reflexiva[r]
	and
	totalidad[r]
}

pred antireflexiva[r:Relacion] {
	r.rel
}

pred ordenEstricto[r:Relacion] {
	antisimetrica[r]
	and
	transitiva[r]
	and
	not reflexiva[r]
}

run preorden for 5 but 1 Relacion
run ordenParcial for 5 but 1 Relacion
run ordenTotal for 5 but 1 Relacion
run ordenEstricto for 5 but 1 Relacion
run cosa for 5 but 1 Relacion
