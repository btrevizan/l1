type variable = string

type newVarGenerator = unit -> newVariable
type newVariable = NewVariable of string * newVarGenerator

type typeDef = TypeInt 
			| TypeBool 
			| TypeId of string 
			| TypeFn of typeDef * typeDef 
			| TypeList of typeDef
			| TypePair of typeDef * typeDef 

type binaryOperator = Sum 
					| Sub 
					| Mult 
					| Div 
					| Equal 
					| Diff 
					| Less 
					| LessOrEqual 
					| Greater 
					| GreaterOrEqual 
					| And 
					| Or

type unaryOperator = Not

type value = ValueNum of int
			| ValueBool of bool
			| ValueNil 
			| ValueCons of value * value
			| ValueRaise
			| VPair of value * value

type expression = Nval of int
				| Bval of bool
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
				| Letrec of variable * variable * expression * expression
				| Nil
				| Cons of expression * expression
				| Hd of expression
				| Tl of expression
				| Isempty of expression
				| Raise
				| Try of expression * expression

type env = (variable * value) list

type typeEnv = (variable * typeDef) list

type typeEquations = (typeDef * typeDef) list