open util/ordering[State] 

// El dominio del problema ---------
abstract sig Object { hits: set Object, protects:set Object}
 
one sig Mom, Dad, Preso, Cop, Boy1, Boy2, Girl1, Girl2, Boat
       extends Object { }

fact hitting { hits = 
	(Preso -> (Object-Cop-Boat-Preso) )+
	(Mom -> Boy1) + (Mom ->Boy2)+
	(Dad -> Girl1) + (Dad  -> Girl2)
}

fact protecting { protects = 
	(Cop -> Preso) + 
	(Mom -> Dad)  +
	(Dad -> Mom) 
	
}
// La dinámica --------------------
// Espacio de estado
sig State {
	near: set Object, 
	far: set Object 
	} 

// Estado inicial
fact initialState {
	let s0 = first[] | s0.near = Object && no s0.far 
}

// Transición
pred crossRiver [ from, from', to, to': set Object ] { 
	some item: from - Boat - Mom - Dad - Cop|
		some adult: from&(Mom+Dad+Cop)|
			(
				from' = from -(from-(from.protects)).hits - Boat - item - adult &&
				to' = to - (to-(to.protects)).hits+ ((item + Boat + adult) - (adult+item).hits)
			)
			||
			(
				from' = from -(from-(from.protects)).hits - Boat - adult &&
				to' = to - (to-(to.protects)).hits +Boat + adult
			)
			||
			(
				some adult2: from&(Mom+Dad+Cop)|
				from' = from -(from-(from.protects)).hits - Boat - adult2 - adult &&
				to' = to - (to-(to.protects)).hits+ adult2 + Boat + adult
			)
	} 

fact stateTransition {
	all s: State, s': next[s] |
		( Boat in s.near => crossRiver [ s.near, s'.near, s.far, s'.far ] ) &&
		( Boat in s.far => crossRiver [ s.far, s'.far, s.near, s'.near ] )
}

// Estado Final
pred solvePuzzle[] {
  some s: State | s.far = Object 
}

// Ejecución
run solvePuzzle for 18 State 

