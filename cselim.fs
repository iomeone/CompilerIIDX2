#indent "off"
module Cselim

open KNormal

let rec find x env =
	match env with
	| (id,data)::ys -> (if data = x then (Var id) else find x ys)
	| [] -> raise Not_found;;

let rec replace env tree =
	match tree with
	| Unit -> Unit
	| Int(i) -> Int(i)
	| Float(d) -> Float(d)
	| Neg _ -> (try (find tree env) with _ -> tree)
	| Add _ -> (try (find tree env) with _ -> tree)
	| Sub _  -> (try (find tree env) with _ -> tree)
	| Mul _ -> (try (find tree env) with _ -> tree)
	| Div _ -> (try (find tree env) with _ -> tree)
	| FNeg _ -> (try (find tree env) with _ -> tree)
	| FAdd _ -> (try (find tree env) with _ -> tree)
	| FSub _ -> (try (find tree env) with _ -> tree)
	| FMul _ -> (try (find tree env) with _ -> tree)
	| FDiv _ -> (try (find tree env) with _ -> tree)
	| IfEq (a,b, e1, e2) -> IfEq (a, b, (replace env e1), (replace env e2))
	| IfLE (a,b, e1, e2) -> IfLE (a, b, (replace env e1), (replace env e2))
	| Let ((x,t),e1,e2) -> Let ((x,t), (replace env e1), (replace env e2))
	| Var _ -> tree
	| LetRec (f,e) -> LetRec (f,(replace env e))
	| App _ -> (try (find tree env) with _ -> tree)
	| Tuple _ -> (try (find tree env) with _ -> tree)
	| LetTuple _ -> (try (find tree env) with _ -> tree)
	| Get _ -> (try (find tree env) with _ -> tree)
	| Put _ -> (try (find tree env) with _ -> tree)
	| ExtArray _ -> (try (find tree env) with _ -> tree)
	| ExtFunApp _ -> (try (find tree env) with _ -> tree)
	| Print _ -> (try (find tree env) with _ -> tree)
	| PrintShort _ -> (try (find tree env) with _ -> tree)
	| Scan _ -> (try (find tree env) with _ -> tree)
	| Sqrt _ -> (try (find tree env) with _ -> tree)
	
let rec g env tree = (*共通部分式除去。渡される木はα変換済み*)
	match tree with
  | Unit -> Unit
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Neg(x) -> Neg(x)
  | Add(x, y) -> Add(x, y)
  | Sub(x, y) -> Sub(x, y)
  | Mul(x, y) -> Mul(x, y)
  | Div(x, y) -> Div(x, y)
  | FNeg(x) -> FNeg(x)
  | FAdd(x, y) -> FAdd(x, y)
  | FSub(x, y) -> FSub(x, y)
  | FMul(x, y) -> FMul(x, y)
  | FDiv(x, y) -> FDiv(x, y)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
  | Let((x, t), e1, e2) -> 
			let e1' = replace env e1 in
			Let ((x,t), e1', g ((x,e1')::env) e2)
  | Var(x) -> Var(x)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> 
			let e1' = replace env e1 in
      LetRec({ name = (x, t); args = yts; body = e1' }, g env e2)
  | App(x, ys) -> App(x, ys)
  | Tuple(xs) -> Tuple(xs)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, e)
  | Get(x, y) -> Get(x, y)
  | Put(x, y, z) -> Put(x, y, z)
  | ExtArray(x) -> ExtArray(x)
  | ExtFunApp(x, ys) -> ExtFunApp(x, ys)
	| Print(x) -> Print(x)
	| PrintShort(x) -> PrintShort(x)
	| Scan(x) -> Scan(x)
	| Sqrt(x) -> Sqrt(x)

let f = g []
