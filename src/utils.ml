open definitons

let varGenerator =
  let rec generator n = newVariable("#x" ^ string_of_int n, generator (n + 1)) in generator 0
  
let lookup environment x = 
	(snd (List.find 
			(fun (var, val) -> String.compare var x == 0) 
			environment
		 )
	)