type variable = string

type typeDef = TypeInt | TypeBool | TypeList of typeDef | TypeFn of typeDef * typeDef | TypeId of string

type binaryOperator = Sum | Sub | Mult | Div | Equal | Diff | Less | LessOrEqual | Greater | GreaterOrEqual | And | Or

type unaryOperator = Not

type value = ValueNum of int
			| ValueBool of bool
			| ValueNil 
			| ValueCons of value * value
			| ValueRaise
			| VPair of value * value

type expression = Nval of int
				| Nbool of bool
				| Binop of binaryOperator * expression * expression
				| Unop of unaryOperator * expression
				| Pair of expression * expression
				| Fst of expression
				| Snd of expression
				| If of expression * expression * expression
				| Id of variable
				| App of expression * expression
				| Fn of variable * expression
				| Let of variable * expression * expression
				| Letrec of variable * expression * variable * expression * expression
				| Nil
				| Cons of expression * expression
				| Hd of expression
				| Tl of expression
				| Raise
				| Try of expression * expression

type env = (variable * value) list

type typeEnv = (variable * typeDef) list

type typeEquations = (typeDef * typeDef) list