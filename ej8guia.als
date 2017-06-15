open util/ordering[State]

abstract sig Object {
    fajar: set Object
   }

one sig Nene1, Nene2, Padre, Nena1, Nena2, Madre, Cobani, Preso, Balsa extends Object {}

fact Fajar {
no Preso.fajar //	Preso.fajar = Object - Cobani - Preso - Balsa
no Padre.fajar 	//Padre.fajar = Nena1 + Nena2
no Madre.fajar 	//Madre.fajar = Nene1 + Nene2
	no Nene1.fajar
	no Nene2.fajar
	no Nena1.fajar
	no Nena2.fajar
	no Cobani.fajar
no Balsa.fajar
}

sig State {
    near: set Object,
    far: set Object,
   }

fact initialState {
    let s0 = first[] |
        s0.near = Object && no s0.far
   }

pred crossRiver[from,from',to,to':set Object] {
        (some item: from - Balsa | 
            (from' = from - Balsa - item) &&
            (to' = to + Balsa + item)
        )
        ||
        (some item, item2: from - Balsa |
            (from' = from - item - item2 - Balsa) && 
             (to' = to + item + item2 + Balsa) 
        )
}	

fact stateTransition {
    all s: State, s': next[s] | 
    ( Balsa in s.near => 
        crossRiver[s.near,s'.near,s.far,s'.far] ) 
    || 
    ( Balsa in s.far => 
        crossRiver[s.far,s'.far,s.near,s'.near ] )
//    and
//         all x:Object | x in s.near or x in s.far
}

pred solvePuzzle { 
//    some s: State | s.far = Object
   }

run solvePuzzle for 5 State
//check solvePuzzle for 24 state

pred cosaman[x: Object]{
		    x = Padre or x = Madre or x = Cobani
}

run crossRiver for 5 State
run cosaman for 10 State
