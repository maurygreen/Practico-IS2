sig Interprete {}
sig Cancion {}
sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
   }{
	~interpretaciones.interpretaciones in iden
	interpretaciones.interpretes = canciones
	canciones.interpretaciones = interpretes
   }

pred addsong[cat,cat':Catalogo, s:Cancion, i:Interprete]{
	cat'.canciones = cat.canciones + s
	and
	cat'.interpretes = cat.interpretes + i
	and
	cat'.interpretaciones = cat.interpretaciones + s->i
}

pred deletesong[cat,cat':Catalogo, s:Cancion, i:Interprete]{
	cat'.canciones = cat.canciones - s
	and
	cat'.interpretes = cat.interpretes - i
	and
	cat'.interpretaciones = cat.interpretaciones - s->i
}

//fun puto [cat: Catalogo]:  {
//	canciones.interpretaciones
//}

run addsong for 5 but 1 Catalogo
run deletesong for 5 but 1 Catalogo
