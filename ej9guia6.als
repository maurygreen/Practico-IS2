sig Mins {}
abstract sig People {
	demora: set Mins
}

one sig Indiana, Novia, Padre, Suegro extends People {}

fact Demorama {
	#Indiana.demora = 5
	#Novia.demora = 10
	#Padre.demora = 20
	#Suegro.demora = 25
}

pred sumTime [x: People]{
	#(x.demora) > 7
}

run sumTime for 25 Mins

assert eso {
	some x: People | #x.demora = 5
}

check eso
