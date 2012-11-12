#indent "off"
module Emit
open Asm
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop

(*external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"*)

[<System.Runtime.InteropServices.DllImport(@"float.dll", EntryPoint="getftoi")>]
	extern int getftoi(double size);
[<System.Runtime.InteropServices.DllImport(@"float.dll", EntryPoint="gethi")>]
	extern int gethi(double size);
[<System.Runtime.InteropServices.DllImport(@"float.dll", EntryPoint="getlo")>]
	extern int getlo(double size);

(*フラグ*)
let arrayset = ref 0;;
let farrayset = ref 0;;
let ftoiflag = ref 0;;
let itofflag = ref 0;;
let floorflag = ref 0;;
let mullabel = ref 0;;
let scanlabel = ref 0;;

let stackset = ref Set.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x = 
  stackset := Set.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x = 
  stackset := Set.add x !stackset;
  if not (List.mem x !stackmap) then
		stackmap := !stackmap @ [x]
(*    (let pad = 
       if List.length !stackmap % 2 = 0 then [] else [Id.gentmp Type.Int] in
       stackmap := !stackmap @ pad @ [x; x])*)
let succ x = x + 1
let locate x = 
  let rec loc = function 
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
    loc !stackmap
let offset x = 1 * (List.head (locate x)+1)
let stacksize () = ((List.length !stackmap + 1) * 1)

let reg r = 
  if is_reg r 
(*   then String.sub r 1 (String.length r - 1) *)
  then r.Substring(1, (String.length r - 1))
  else r 

let load_label r label =
  "\taddi\t" ^ (reg r) ^ ", r0, h16(" ^ label ^ ")\n" ^
	"\tslli\t" ^ (reg r) ^ ", " ^ (reg r) ^ ", 16\n" ^
  "\taddi\t" ^ (reg r) ^ ", " ^ (reg r) ^ ", l16(" ^ label ^ ")\n"

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys = 
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) :: 
	    shuffle sw (List.map (function 
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

(*2の累乗判定*)
let rec twopowers_sub n b c =
	if (n < b) then -1 
	else (if(n = b) then c else twopowers_sub n (b*2) (c+1))
let rec twopowers n =
	twopowers_sub n 1 0;;
	

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
    (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  (*即値代入*)
  | (NonTail(x), Li(i)) when i >= -32768 && i < 32768 -> 
      Printf.fprintf oc "\tmvli\t%s, %d\n" (reg x) i
  | (NonTail(x), Li(i)) ->(*大きすぎる即値*)
      let n = i >>> 16 in
      let m = i ^^^ (n <<< 16) in
				Printf.fprintf oc "\tmvhi\t%s, %d\n" (reg x) n;
				Printf.fprintf oc "\tmvli\t%s, %d\n" (reg x) m
(*      let r = reg x in
				Printf.fprintf oc "\taddi\t%s, r0, %d\t#%s = %d\n" r n r i;
				Printf.fprintf oc "\tslli\t%s, %s, 16\n" r r;
				if (m >>> 15)=1 then 
					let m1 = m ^^^ (1 <<< 15) in
						Printf.fprintf oc "\taddi\t%s, %s, %d\n" r r m1;
						Printf.fprintf oc "\taddi\t%s, %s, 32767\n" r r;
						Printf.fprintf oc "\taddi\t%s, %s, 1\n" r r
				else
					Printf.fprintf oc "\toori\t%s, %s, %d\n" r r m*)
  | (NonTail(x), FLi(i)) ->
      let n = i >>> 16 in
      let m = i ^^^ (n <<< 16) in
				Printf.fprintf oc "\tfmvhi\t%s, %d\n" (reg x) n;
				Printf.fprintf oc "\tfmvli\t%s, %d\n" (reg x) m
(*      let r = reg x in
				Printf.fprintf oc "\taddi\t%s, r0, %d\t#%s = %08x\n" reg_tmp n reg_tmp i;
				Printf.fprintf oc "\tslli\t%s, %s, 16\n" reg_tmp reg_tmp;
				if (m >>> 15)=1 then 
					let m1 = m ^^^ (1 <<< 15) in
						Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_tmp reg_tmp m1;
						Printf.fprintf oc "\taddi\t%s, %s, 32767\n" reg_tmp reg_tmp;
						Printf.fprintf oc "\taddi\t%s, %s, 1\n" reg_tmp reg_tmp
				else
					Printf.fprintf oc "\toori\t%s, %s, %d\n" reg_tmp reg_tmp m;
				Printf.fprintf oc "\tmif\t%s, %s, r0\n" r reg_tmp*)
//      let s = load_label reg_tmp l in
 //     Printf.fprintf oc "%s\tldf\t%s, %s, 0\n" s (reg x) reg_tmp
  | (NonTail(x), SetL(Id.L(y))) -> 
      let s = load_label x y in
      Printf.fprintf oc "%s" s
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) -> Printf.fprintf oc "\taddi\t%s, %s, 0\n" (reg x) (reg y)
			(*符号反転*)
  | (NonTail(x), Neg(y)) -> Printf.fprintf oc "\tsub\t%s, r0, %s\n" (reg x) (reg y)
	(*追加した命令*)
	| (NonTail(x), Print(y)) -> 
			Printf.fprintf oc "\tprt\t%s, 1\n" (reg y)
	| (NonTail(x), PrintShort(y)) -> 
			Printf.fprintf oc "\tctds\t%s, %s\n" reg_tmp (reg y);
			Printf.fprintf oc "\tprtvc\t%s, 4\n" reg_tmp;
			Printf.fprintf oc "\tprtcc\t%s, 2\n" reg_tmp;
			Printf.fprintf oc "\tprt\t%s, 1\n" reg_tmp
	| (NonTail(x), Scan(y)) -> 
			Printf.fprintf oc "scanlabel.%d:\n" !scanlabel;
			Printf.fprintf oc "\tscns\t%s, %s, 1\n" (reg x) (reg y);
			Printf.fprintf oc "\tjmpics\tscanlabel.%d\n" !scanlabel;
			scanlabel := !scanlabel + 1
	| (NonTail(x), Sqrt(y)) -> 
			Printf.fprintf oc "\tfsqr\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Add(y, V(z))) ->  
      Printf.fprintf oc "\tadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Add(y, C(z))) -> 
      Printf.fprintf oc "\taddi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Sub(y, V(z))) -> 
      Printf.fprintf oc "\tsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Sub(y, C(z))) -> 
      Printf.fprintf oc "\tsubi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Mul(y, V(z))) ->  
			Printf.fprintf oc "\taddi\t%s, r0, 0\n" reg_tmp2;
			for i = 1 to 32 do
				Printf.fprintf oc "\tsllis\tr0, %s, %d\n" (reg z) i;
				Printf.fprintf oc "\tsllics\t%s, %s, %d\n" reg_tmp (reg y) (32-i);
			  Printf.fprintf oc "\taddcs\t%s, %s, %s\n" reg_tmp2 reg_tmp2 reg_tmp
			done;
			Printf.fprintf oc "\taddi\t%s, %s, 0\n" (reg x) reg_tmp2
  | (NonTail(x), Mul(y, C(z))) -> 
			let sv = twopowers z in
			if (sv = -1) then(
				Printf.fprintf oc "\taddi\t%s, r0, 0\n" reg_tmp2;
				for i = 0 to 31 do
					if ((z >>> i) &&& 1) > 0 then(
			      Printf.fprintf oc "\tslli\t%s, %s, %d\n" reg_tmp (reg y) i;
			      Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp2 reg_tmp2 reg_tmp)
					else ()
				done;
				Printf.fprintf oc "\taddi\t%s, %s, 0\n" (reg x) reg_tmp2
			)
			else
	      Printf.fprintf oc "\tslai\t%s, %s, %d\n" (reg x) (reg y) sv
  | (NonTail(x), Div(y, V(z))) ->  
      Printf.fprintf oc "\tinv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Div(y, C(z))) -> 
			let sv = twopowers z in
			if (sv = -1) then
		    Printf.fprintf oc "\tinvi\t%s, %s, %d\n" (reg x) (reg y) z
			else
		    Printf.fprintf oc "\tsrli\t%s, %s, %d\n" (reg x) (reg y) sv
  | (NonTail(x), Slw(y, V(z))) -> 
      Printf.fprintf oc "\tsll\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, C(z))) -> 
      Printf.fprintf oc "\tslli\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Lwz(y, V(z))) ->
			Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
      Printf.fprintf oc "\tldw\t%s, %s, 0\n" (reg x) reg_tmp
  | (NonTail(x), Lwz(y, C(z))) -> 
      Printf.fprintf oc "\tldw\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(_), Stw(x, y, V(z))) ->
			Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
      Printf.fprintf oc "\tstw\t%s, %s, 0\n" (reg x) reg_tmp
  | (NonTail(_), Stw(x, y, C(z))) -> 
      Printf.fprintf oc "\tstw\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) -> Printf.fprintf oc "\tfmov\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FNeg(y)) -> 
      Printf.fprintf oc "\tfneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FAdd(y, z)) -> 
      Printf.fprintf oc "\tfadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FSub(y, z)) -> 
      Printf.fprintf oc "\tfsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FMul(y, z)) -> 
      Printf.fprintf oc "\tfmul\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FDiv(y, z)) -> 
      Printf.fprintf oc "\tfinv\t%s, %s, f0\n" reg_ftmp (reg z);
      Printf.fprintf oc "\tfmul\t%s, %s, %s\n" (reg x) (reg y) reg_ftmp
  | (NonTail(x), Lfd(y, V(z))) ->
			Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
      Printf.fprintf oc "\tldf\t%s, %s, 0\n" (reg x) reg_tmp
  | (NonTail(x), Lfd(y, C(z))) -> 
      Printf.fprintf oc "\tldf\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(_), Stfd(x, y, V(z))) ->
			Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
      Printf.fprintf oc "\tstf\t%s, %s, 0\n" (reg x) reg_tmp
  | (NonTail(_), Stfd(x, y, C(z))) ->
      Printf.fprintf oc "\tstf\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(_), Comment(s)) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
      when List.mem x allregs && not (Set.contains y !stackset) ->
				save y;
				Printf.fprintf oc "\tstw\t%s, %s, -%d\n" (reg x) reg_sp (offset y)
  | (NonTail(_), Save(x, y)) 
      when List.mem x allfregs && not (Set.contains y !stackset) ->
      savef y;
				Printf.fprintf oc "\tstf\t%s, %s, -%d\n" (reg x) reg_sp (offset y)
  | (NonTail(_), Save(x, y)) -> 
      if Set.contains y !stackset then 
        ()
      else
        failwith "fatal error at emit.fs (id:2)"
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      Printf.fprintf oc "\tldw\t%s, %s, -%d\n" (reg x) reg_sp (offset y)
  | (NonTail(x), Restore(y)) ->
      if List.mem x allfregs then
        Printf.fprintf oc "\tldf\t%s, %s, -%d\n" (reg x) reg_sp (offset y)
      else
        failwith "fatal error at emit.fs (id:1)"
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ as exp)) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      Printf.fprintf oc "\tjmp\tr31\n";
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Print _ | PrintShort _ | Scan _ | Sqrt _ | Add _ | Sub _ | Mul _ | Div _ | Slw _ |
            Lwz _ as exp)) -> 
      g' oc (NonTail(regs.[0]), exp);
      Printf.fprintf oc "\tjmp\tr31\n";
  | (Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ |
            Lfd _ as exp)) ->
      g' oc (NonTail(fregs.[0]), exp);
      Printf.fprintf oc "\tjmp\tr31\n";
  | (Tail, (Restore(x) as exp)) ->
      (match locate x with
	 | [i] -> g' oc (NonTail(regs.[0]), exp)
	 | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.[0]), exp)
	 | _ -> failwith "fatal error at emit.fs (id:3)");
      Printf.fprintf oc "\thlt\n";
		(*レジスタ比較*)
  | (Tail, IfEq(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "jmpeq" "jmpine"
		(*即値比較*)
  | (Tail, IfEq(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_tail_if oc e1 e2 "jmpeq" "jmpine"
  | (Tail, IfLE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "jmple" "jmpigt"
  | (Tail, IfLE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_tail_if oc e1 e2 "jmple" "jmpigt"
  | (Tail, IfGE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "jmpge" "jmpilt"
  | (Tail, IfGE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_tail_if oc e1 e2 "jmpge" "jmpilt"
  | (Tail, IfFEq(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfsubs\tf0, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "jmpeq" "jmpine"
  | (Tail, IfFLE(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfsubs\tf0, %s, %s\n" (reg x) (reg y);
      g'_tail_if oc e1 e2 "jmple" "jmpigt"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmpeq" "jmpine"
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmpeq" "jmpine"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmple" "jmpigt"
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmple" "jmpigt"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
      Printf.fprintf oc "\tsubs\tr0, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmpge" "jmpilt"
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
      Printf.fprintf oc "\tsubis\tr0, %s, %d\n" (reg x) y;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmpge" "jmpilt"
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfsubs\tf0, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmpeq" "jmpine"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
      Printf.fprintf oc "\tfsubs\tf0, %s, %s\n" (reg x) (reg y);
      g'_non_tail_if oc (NonTail(z)) e1 e2 "jmple" "jmpigt"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [(x, reg_cl)] ys zs;
      Printf.fprintf oc "\tldw\t%s, %s, 0\n" (reg reg_sw) (reg reg_cl);
      Printf.fprintf oc "\tjmp\t%s\n" (reg reg_sw);
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      Printf.fprintf oc "\tjmpi\t%s\n" x
	(*クロージャ有り関数呼び出し*)
  | (NonTail(a), CallCls(x, ys, zs)) ->
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
				(*スタックフレームの追加*)
				Printf.fprintf oc "\tstw\t%s, %s, -%d\n" reg_lr reg_sp ss;(*リンクレジスタの退避*)
				Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;(*スタックポインタの更新*)
				
				Printf.fprintf oc "\tldw\t%s, %s, 0\n" reg_tmp (reg reg_cl); (*クロージャアドレスから飛ぶ先のアドレスをロード*)
				Printf.fprintf oc "\tcal\t%s\n" reg_tmp;

				Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;(*スタックポインタの復帰*)
				Printf.fprintf oc "\tldw\t%s, %s, -%d\n" reg_lr reg_sp ss;(*リンクレジスタの復帰*)
				(if List.mem a allregs && a <> regs.[0] then 
					 Printf.fprintf oc "\tmov\t%s, %s\n" (reg a) (reg regs.[0]) 
				 else if List.mem a allfregs && a <> fregs.[0] then 
					 Printf.fprintf oc "\tfmov\t%s, %s\n" (reg a) (reg fregs.[0]));
	(*関数呼び出し*)
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) -> 
      g'_args oc [] ys zs;
      let ss = stacksize () in
				(*スタックフレームの追加*)
				Printf.fprintf oc "\tstw\t%s, %s, -%d\n" reg_lr reg_sp ss;(*リンクレジスタの退避*)
				Printf.fprintf oc "\taddi\t%s, %s, -%d\n" reg_sp reg_sp ss;(*スタックポインタの更新*)

				Printf.fprintf oc "\tcali\t%s\n" x;(*関数呼び出し*)
				if x="external_create_array" then arrayset := 1 else(
				if x="external_create_float_array" then farrayset := 1 else (
				if x="external_float_of_int" then itofflag := 1 else (
				if x="external_int_of_float" then ftoiflag := 1 else (
				if x="external_floor" then floorflag := 1 else ()))));

				Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;(*スタックポインタの復帰*)
				Printf.fprintf oc "\tldw\t%s, %s, -%d\n" reg_lr reg_sp ss;(*リンクレジスタの復帰*)
				(if List.mem a allregs && a <> regs.[0] then
					 Printf.fprintf oc "\tmov\t%s, %s\n" (reg a) (reg regs.[0])
				 else if List.mem a allfregs && a <> fregs.[0] then
					 Printf.fprintf oc "\tfmov\t%s, %s\n" (reg a) (reg fregs.[0]));
and g'_tail_if oc e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
    Printf.fprintf oc "\t%s\t%s\n" bn b_else;
    let stackset_back = !stackset in
      g oc (Tail, e1);
      Printf.fprintf oc "%s:\n" b_else;
      stackset := stackset_back;
      g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    Printf.fprintf oc "\t%s\t%s\n" bn b_else;
    let stackset_back = !stackset in
      g oc (dest, e1);
      let stackset1 = !stackset in
	Printf.fprintf oc "\tjmpi\t%s\n" b_cont;
	Printf.fprintf oc "%s:\n" b_else;
	stackset := stackset_back;
	g oc (dest, e2);
	Printf.fprintf oc "%s:\n" b_cont;
	let stackset2 = !stackset in
	  stackset := Set.intersect stackset1 stackset2
and g'_args oc x_reg_cl ys zs = 
(*引数を格納するためのスワップ*)
  let (i, yrs) = 
    List.fold
      (fun (i, yrs) y -> (i + 1, (y, regs.[i]) :: yrs))
      (0, x_reg_cl) ys in
    List.iter
      (fun (y, r) -> Printf.fprintf oc "\taddi\t%s, %s, 0\n" (reg r) (reg y))
      (shuffle reg_sw yrs);
    let (d, zfrs) = 
      List.fold
	(fun (d, zfrs) z -> (d + 1, (z, fregs.[d]) :: zfrs))
	(0, []) zs in
      List.iter
        (fun (z, fr) -> Printf.fprintf oc "\tfmov\t%s, %s\n" (reg fr) (reg z))
	(shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  stackset := Set.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Prog(data, fundefs, e)) =
  Printf.eprintf "generating assembly...\n";
  (if data <> [] then
    (Printf.fprintf oc "\t.data\n\t.literal8\n";
     List.iter
       (fun (Id.L(x), d) ->
				 Printf.fprintf oc "\t.align 3\n";
				 Printf.fprintf oc "%s:\t # %f\n" x d;
				 Printf.fprintf oc "\t.long\t%d\n" (getftoi d))
//				 Printf.fprintf oc "\t.long\t%d\n" (getlo d))
						 data));
(*  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.globl  _min_caml_start\n";
  Printf.fprintf oc "\t.align 2\n";*)
(*メインポイントまで移動命令*)
	(if List.length fundefs > 0 then Printf.fprintf oc "\tjmpi\t_min_caml_start\n" else ());
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc "_min_caml_start: # main entry point\n";
(*プログラム開始時の処理*)
	Printf.fprintf oc "\taddi\tr1,r0,1\n";
	Printf.fprintf oc "\tslli\tr1,r1,19\n";(*スタックポインタの開始位置*)
	Printf.fprintf oc "\taddi\tr4,r0,0\n"; (*heap register*)
(*	Printf.fprintf oc "\tjmpi\t_min_caml_start\n";*)
(*  Printf.fprintf oc "\tmflr\tr0\n";
  Printf.fprintf oc "\tstmw\tr30, -8(r1)\n";
  Printf.fprintf oc "\tstw\tr0, 8(r1)\n";
  Printf.fprintf oc "\tstwu\tr1, -96(r1)\n";*)
  Printf.fprintf oc "   # main program start\n";
  stackset := Set.empty;
  stackmap := [];
  g oc (NonTail("_R_0"), e);
  Printf.fprintf oc "   # main program end\n";
(*プログラム終了時の処理*)
  Printf.fprintf oc "\thlt\n";
(*create_array*)
	(if !arrayset=1 then (
		Printf.fprintf oc "external_create_array:\n";
		Printf.fprintf oc "\tmov\tr6, r2\n";
		Printf.fprintf oc "\tmov\tr2, r4\n";
		Printf.fprintf oc "\tsubis\tr0, r6, 1\n";
		Printf.fprintf oc "\tjmpmi\tr31\n";
		Printf.fprintf oc "create_array_loop:\n";
		Printf.fprintf oc "\tstw\tr5, r4, 0\n";
		Printf.fprintf oc "\taddi\tr4, r4, 1\n";
		Printf.fprintf oc "\tsubis\tr6, r6, 1\n";
		Printf.fprintf oc "\tjmpine\tcreate_array_loop\n";
		Printf.fprintf oc "\tjmp\tr31\n") else ());
	(if !farrayset=1 then(
		Printf.fprintf oc "external_create_float_array:\n";
		Printf.fprintf oc "\tmov\tr6, r2\n";
		Printf.fprintf oc "\tmov\tr2, r4\n";
		Printf.fprintf oc "\tsubis\tr0, r6, 1\n";
		Printf.fprintf oc "\tjmpmi\tr31\n";
		Printf.fprintf oc "\tmfi\tr5, f1, r0\n";
		Printf.fprintf oc "create_float_array_loop:\n";
		Printf.fprintf oc "\tstw\tr5, r4, 0\n";
		Printf.fprintf oc "\taddi\tr4, r4, 1\n";
		Printf.fprintf oc "\tsubis\tr6, r6, 1\n";
		Printf.fprintf oc "\tjmpine\tcreate_float_array_loop\n";
		Printf.fprintf oc "\tjmp\tr31\n") else ());
	(if !itofflag=1 then(
		Printf.fprintf oc "external_float_of_int:\n";
		Printf.fprintf oc "\tsubis\tr0, r2, 0\n";
		Printf.fprintf oc "\tjmpilt\tfloat_of_int.1\t\t#minus\n";
		Printf.fprintf oc "\tmvhi\tr32, 128\t# r32 = 8388608\n";
		Printf.fprintf oc "\tmvhi\tr33, 19200\t# r33 = 0x4B000000\n";
		Printf.fprintf oc "\tsubs\tr0, r2, r32\n";
		Printf.fprintf oc "\tjmpige\tfloat_of_int.2\t\t#large\n";
		Printf.fprintf oc "\tadd\tr34, r2, r33\n";
		Printf.fprintf oc "\tfsub\tf1, f34, f33\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "float_of_int.2:\n";
		Printf.fprintf oc "\tfmov\tf3, f0\n";
		Printf.fprintf oc "float_of_int.21:\n";
		Printf.fprintf oc "\tfadd\tf3, f3, f33\n";
		Printf.fprintf oc "\tsub\tr2, r2, r32\n";
		Printf.fprintf oc "\tsubs\tr0, r2, r32\n";
		Printf.fprintf oc "\tjmpigt\tfloat_of_int.21\n";
		Printf.fprintf oc "\tadd\tr34, r2, r33\t# f3 = m*8388608.0  r2 = n\n";
		Printf.fprintf oc "\tfsub\tf1, f34, f33\n";
		Printf.fprintf oc "\tfadd\tf1, f1, f3\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "float_of_int.1:\n";
		Printf.fprintf oc "\tsubs\tr2, r0, r2\n";
		Printf.fprintf oc "\tmvhi\tr32, 128\t# r32 = 8388608\n";
		Printf.fprintf oc "\tmvhi\tr33, 19200\t# r33 = 0x4B000000\n";
		Printf.fprintf oc "\tsubs\tr0, r2, r32\n";
		Printf.fprintf oc "\tjmpige\tfloat_of_int.3\t\t#large\n";
		Printf.fprintf oc "\tadd\tr34, r2, r33\n";
		Printf.fprintf oc "\tfsub\tf1, f34, f33\n";
		Printf.fprintf oc "\tfneg\tf1, f1\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "float_of_int.3:\n";
		Printf.fprintf oc "\tfmov\tf3, f0\n";
		Printf.fprintf oc "float_of_int.31:\n";
		Printf.fprintf oc "\tfadd\tf3, f3, f33\n";
		Printf.fprintf oc "\tsub\tr2, r2, r32\n";
		Printf.fprintf oc "\tsubs\tr0, r2, r32\n";
		Printf.fprintf oc "\tjmpigt\tfloat_of_int.31\n";
		Printf.fprintf oc "\tadd\tr34, r2, r33\t# f3 = m*8388608.0  r2 = n\n";
		Printf.fprintf oc "\tfsub\tf1, f34, f33\n";
		Printf.fprintf oc "\tfadd\tf1, f1, f3\n";
		Printf.fprintf oc "\tfneg\tf1, f1\n";
		Printf.fprintf oc "\tjmp\tr31\n")else ());
	(if !ftoiflag=1 then(
		Printf.fprintf oc "external_int_of_float:\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f0\n";
		Printf.fprintf oc "\tjmpilt\tint_of_float.1 	#minus\n";
		Printf.fprintf oc "\tmvhi\tr33, 19200\t# r33 = 0x4B000000\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f33\n";
		Printf.fprintf oc "\tjmpige\tint_of_float.2	#large\n";
		Printf.fprintf oc "\tfadd\tf34, f1, f33\n";
		Printf.fprintf oc "\tsub\tr2, r34, r33\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "int_of_float.2:\n";
		Printf.fprintf oc "\taddi\tr6, r0, 0\n";
		Printf.fprintf oc "\tmvhi\tr32, 128\t# r32 = 8388608\n";
		Printf.fprintf oc "int_of_float.21:\n";
		Printf.fprintf oc "\tadd\tr6, r6, r32\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f33\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f33\n";
		Printf.fprintf oc "\tjmpigt\tint_of_float.21\n";
		Printf.fprintf oc "\tfadd\tf34, f1, f33\n";
		Printf.fprintf oc "\tsub\tr2, r34, r33\n";
		Printf.fprintf oc "\tadd\tr2, r2, r6\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "int_of_float.1:\n";
		Printf.fprintf oc "\tfneg\tf1, f1\n";
		Printf.fprintf oc "\tmvhi\tr33, 19200\t# r33 = 0x4B000000\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f33\n";
		Printf.fprintf oc "\tjmpige\tint_of_float.3	#large\n";
		Printf.fprintf oc "\tfadd\tf34, f1, f33\n";
		Printf.fprintf oc "\tsub\tr2, r34, r33\n";
		Printf.fprintf oc "\tsub\tr2, r0, r2\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "int_of_float.3:\n";
		Printf.fprintf oc "\taddi\tr6, r0, 0\n";
		Printf.fprintf oc "\tmvhi\tr32, 128\t# r32 = 8388608\n";
		Printf.fprintf oc "int_of_float.31:\n";
		Printf.fprintf oc "\tadd\tr6, r6, r32\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f33\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f33\n";
		Printf.fprintf oc "\tjmpigt\tint_of_float.31\n";
		Printf.fprintf oc "\tfadd\tf34, f1, f33\n";
		Printf.fprintf oc "\tsub\tr2, r34, r33\n";
		Printf.fprintf oc "\tadd\tr2, r2, r6\n";
		Printf.fprintf oc "\tsub\tr2, r0, r2\n";
		Printf.fprintf oc "\tjmp\tr31\n")else ());
	(if !floorflag=1 then(
		Printf.fprintf oc "external_floor:\n";
		Printf.fprintf oc "\tfsubs\tf0, f1, f0\n";
		Printf.fprintf oc "\tmvhi\tr33, 19200\t# r33 = 0x4B000000\n";
		Printf.fprintf oc "\tjmpilt\tfloor.1 \t#minus\n";
		Printf.fprintf oc "\tfsubs\tf0, f33, f1\n";
		Printf.fprintf oc "\tjmplt\tr31	\t# large->return\n";
		Printf.fprintf oc "\tfmov\tf3, f1\n";
		Printf.fprintf oc "\tfadd\tf1, f1, f33\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f33\n";
		Printf.fprintf oc "\tfsubs\tf0, f3, f1\n";
		Printf.fprintf oc "\tjmpilt\tfloor.2\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "floor.2:\n";
		Printf.fprintf oc "\tmvhi\tr34, 16256\t# r34 = 0x3F800000 = 1.0\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f34\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "floor.1:\n";
		Printf.fprintf oc "\tfneg\tf1, f1\n";
		Printf.fprintf oc "\tfsubs\tf0, f33, f1\n";
		Printf.fprintf oc "\tfneglt\tf1, f1\n";
		Printf.fprintf oc "\tjmplt\tr31	\t# large->return\n";
		Printf.fprintf oc "\tfmov\tf3, f1\n";
		Printf.fprintf oc "\tfadd\tf1, f1, f33\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f33\n";
		Printf.fprintf oc "\tfneg\tf1, f1\n";
		Printf.fprintf oc "\tfneg\tf3, f3\n";
		Printf.fprintf oc "\tfsubs\tf0, f3, f1\n";
		Printf.fprintf oc "\tjmpilt\tfloor.3\n";
		Printf.fprintf oc "\tjmp\tr31\n";
		Printf.fprintf oc "floor.3:\n";
		Printf.fprintf oc "\tmvhi\tr34, 16256\t# r34 = 0x3F800000 = 1.0\n";
		Printf.fprintf oc "\tfsub\tf1, f1, f34\n";
		Printf.fprintf oc "\tjmp\tr31\n")else ())
(*  Printf.fprintf oc "\tmr\tr3, %s\n" regs.[0]; *)
(*  Printf.fprintf oc "\tlwz\tr1, 0(r1)\n";
  Printf.fprintf oc "\tlwz\tr0, 8(r1)\n";
  Printf.fprintf oc "\tmtlr\tr0\n";
  Printf.fprintf oc "\tlmw\tr30, -8(r1)\n";
  Printf.fprintf oc "\tblr\n"*)
