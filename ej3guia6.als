sig Addr, Data {}

sig Memory {  
    addrs: set Addr  
    map: Addr -> one Data  
   }

sig MainMemory extends Memory {}

sig Cache extends Memory {
	dirty: set addrs
   }

sig System {
	cache: Cache
	main: MainMemory
   }

pred Write [m,m': Memory, d: Data, a: Addr] {
    m'.map = m.map ++ (a-> d)
   }

fact {
    no (MainMemory & Cache)
   }

assert {
    all s: System |
    no s.cache.dirty => s.cache.map in s.main.map
}
