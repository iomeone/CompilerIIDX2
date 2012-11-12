#indent "off"
module Simm
open Asm

let rec g env = function (* ���ߗ�� 16 bit ���l�œK�� *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(i), e) when (-32768 <= i) && (i < 32768) ->
      let e' = g (Map.add x i env) e in
      if List.contains x (fv_asm e') then Let((x, t), Li(i), e') else e'
  | Let(xt, Slw(y, C(i)), e) when Map.containsKey y env -> (* for array access *)
      g env (Let(xt, Li((Map.find y env) <<< i), e))
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* �e���߂� 16 bit ���l�œK�� *)
  | Add(x, V(y)) when Map.containsKey y env -> Add(x, C(Map.find y env))
  | Add(x, V(y)) when Map.containsKey x env -> Add(y, C(Map.find x env))
  | Sub(x, V(y)) when Map.containsKey y env -> Sub(x, C(Map.find y env))
  | Mul(x, V(y)) when Map.containsKey y env -> Mul(x, C(Map.find y env))
  | Mul(x, V(y)) when Map.containsKey x env -> Mul(y, C(Map.find x env))
  | Div(x, V(y)) when Map.containsKey y env -> Div(x, C(Map.find y env))
  | Slw(x, V(y)) when Map.containsKey y env -> Slw(x, C(Map.find y env))
  | Lwz(x, V(y)) when Map.containsKey y env -> Lwz(x, C(Map.find y env))
  | Stw(x, y, V(z)) when Map.containsKey z env -> Stw(x, y, C(Map.find z env))
  | Lfd(x, V(y)) when Map.containsKey y env -> Lfd(x, C(Map.find y env))
  | Stfd(x, y, V(z)) when Map.containsKey z env -> Stfd(x, y, C(Map.find z env))
  | IfEq(x, V(y), e1, e2) when Map.containsKey y env -> 
      IfEq(x, C(Map.find y env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when Map.containsKey y env ->
      IfLE(x, C(Map.find y env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when Map.containsKey y env -> 
      IfGE(x, C(Map.find y env), g env e1, g env e2)
  | IfEq(x, V(y), e1, e2) when Map.containsKey x env -> 
      IfEq(y, C(Map.find x env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when Map.containsKey x env -> 
      IfGE(y, C(Map.find x env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when Map.containsKey x env -> 
      IfLE(y, C(Map.find x env), g env e1, g env e2)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfGE(x, y', e1, e2) -> IfGE(x, y', g env e1, g env e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

(* �g�b�v���x���֐��� 16 bit ���l�œK�� *)
let h { name = l; args = xs; fargs = ys; body = e; ret = t } = 
  { name = l; args = xs; fargs = ys; body = g Map.empty e; ret = t }

(* �v���O�����S�̂� 16 bit ���l�œK�� *)
let f (Prog(data, fundefs, e)) = 
  Prog(data, List.map h fundefs, g Map.empty e)
