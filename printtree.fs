#indent "off"
module Printtree

let rec tab_of_amount amount () = 
    if amount <= 0 then 
			()
    else
			begin
				print_string "\t";
				tab_of_amount (amount-1) ()
			end;;

let rec TypetoString tp = 
	match tp with
	| Type.t.Unit -> "unit"
	| Type.t.Int -> "Int"
	| Type.t.Bool -> "Bool"
	| Type.t.Float -> "Float"
	| Type.t.Fun (_,d) -> TypetoString d
	| Type.t.Tuple _ -> "tuple"
	| Type.t.Array _ -> "Array"
	| Type.t.Var _ -> "Var";;

let rec print_args args () =
	match args with
	| [] -> ()
	| (id,tp)::xs -> Printf.printf "%s(%s) -> " id (TypetoString tp); print_args xs ();;

let rec print_syntax_sub syntax depth () = 
	tab_of_amount depth ();	
  match syntax with
	| Syntax.t.Unit _ -> print_string "UNIT\n"
	| Syntax.t.Bool b -> Printf.printf "BOOL(%s)\n" (if b=true then "true" else "false")
	| Syntax.t.Int i -> Printf.printf "INT(%d)\n" i
	| Syntax.t.Float f -> Printf.printf "FLOAT(%f)\n" f
	| Syntax.t.Not t -> print_string "NOT\n"; print_syntax_sub t (depth+1) ()
	| Syntax.t.Neg t -> print_string "NEG\n"; print_syntax_sub t (depth+1) ()
	| Syntax.t.Add (a,b) -> print_string "ADD\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Sub (a,b) -> print_string "SUB\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Mul (a,b) -> print_string "MUL\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Div (a,b) -> print_string "Div\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.FNeg t -> print_string "FNEG\n"; print_syntax_sub t (depth+1) ()
	| Syntax.t.FAdd (a,b) -> print_string "FADD\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.FSub (a,b) -> print_string "FSUB\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.FMul (a,b) -> print_string "FMUL\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.FDiv (a,b) -> print_string "FDIV\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Eq (a,b) -> print_string "EQ\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.LE (a,b) -> print_string "LE\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.If (a,b,c) -> print_string "IF\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) (); print_syntax_sub c (depth+1) ()
	| Syntax.t.Var t -> Printf.printf "VAR(%s)\n" t
	| Syntax.t.Let ((id,tp),e1,e2) ->
			Printf.printf "Let %s(%s)\n" id (TypetoString tp);
			print_syntax_sub e1 (depth+1) ();
			print_syntax_sub e2 (depth+1) ();
	| Syntax.t.LetRec (f,t) -> 
			print_string "LetRec ";
			let (id,tp) = f.name in Printf.printf "%s = " id;
			print_args f.args ();
			Printf.printf "%s\n" (TypetoString tp);
			print_syntax_sub f.body (depth+1) (); print_syntax_sub t (depth) ()
	| Syntax.t.App (t,tl) -> print_string "APP\n"; print_syntax_sub t (depth+1) (); print_syntax_list tl (depth+1) ()
	| Syntax.t.Tuple tl -> print_string "TUPLE\n"; print_syntax_list tl (depth+1) ()
	| Syntax.t.LetTuple _ -> print_string "LetTuple\n"
	| Syntax.t.Array (a,b) -> print_string "ARRAY\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Get (a,b) -> print_string "GET\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) ()
	| Syntax.t.Put (a,b,c) -> print_string "PUT\n"; print_syntax_sub a (depth+1) (); print_syntax_sub b (depth+1) (); print_syntax_sub c (depth+1) ()
	| Syntax.t.Sqrt t -> print_string "SQRT\n"; print_syntax_sub t (depth+1) ()
	| _ -> print_string "nazo\n"
and print_syntax_list slist depth () =
	match slist with
	| [] -> ()
	| x::xs -> print_syntax_sub x depth ();print_syntax_list xs depth ();;

let print_syntax syntax = 
    print_syntax_sub syntax 0;;

let rec print_knormal_args args () =
	match args with
	| [] -> ()
	| x::xs -> Printf.printf " %s" x; print_knormal_args xs ();;

let rec print_knormal_sub knormal depth () =
	tab_of_amount depth ();	
	match knormal with
	| KNormal.t.Unit -> print_string "UNIT\n"
	| KNormal.t.Int i -> Printf.printf "INT(%d)\n" i
	| KNormal.t.Float f -> Printf.printf "FLOAT(%f)\n" f
	| KNormal.t.Neg id -> Printf.printf "NEG(%s)\n" id
	| KNormal.t.Add (a,b) -> Printf.printf "ADD(%s,%s)\n" a b
	| KNormal.t.Sub (a,b) -> Printf.printf "SUB(%s,%s)\n" a b
	| KNormal.t.FNeg id -> Printf.printf "FNEG(%s)\n" id
	| KNormal.t.FAdd (a,b) -> Printf.printf "FADD(%s,%s)\n" a b
	| KNormal.t.FSub (a,b) -> Printf.printf "FSUB(%s,%s)\n" a b
	| KNormal.t.FMul (a,b) -> Printf.printf "FMUL(%s,%s)\n" a b
	| KNormal.t.FDiv (a,b) -> Printf.printf "FDIV(%s,%s)\n" a b
	| KNormal.t.IfEq (a,b,e1,e2) -> Printf.printf "IF(%s=%s)\n" a b;print_knormal_sub e1 (depth+1) (); print_knormal_sub e2 (depth+1) ();
	| KNormal.t.IfLE (a,b,e1,e2) -> Printf.printf "IF(%s<=%s)\n" a b;print_knormal_sub e1 (depth+1) (); print_knormal_sub e2 (depth+1) ();
	| KNormal.t.Var id -> Printf.printf "VAR(%s)\n" id
	| KNormal.t.Let ((id,tp),e1,e2) ->
			Printf.printf "Let %s(%s)\n" id (TypetoString tp);
			print_knormal_sub e1 (depth+1) ();
			print_knormal_sub e2 (depth+1) ();
	| KNormal.t.LetRec (f,t) -> 
			print_string "LetRec ";
			let (id,tp) = f.name in Printf.printf "%s = " id;
			print_args f.args ();
			Printf.printf "%s\n" (TypetoString tp);
			print_knormal_sub f.body (depth+1) (); print_knormal_sub t (depth) ()
	| KNormal.t.App (t,tl) -> Printf.printf "APP(%s" t; print_knormal_args tl ();print_string ")\n"
	| KNormal.t.Tuple tl -> print_string "TUPLE(";print_knormal_args tl ();print_string ")\n"
	| KNormal.t.Get (a,b) -> Printf.printf "GET(%s,%s)\n" a b
	| KNormal.t.Put (a,b,c) -> Printf.printf "PUT(%s,%s,%s)\n" a b c
	| KNormal.t.ExtArray id -> Printf.printf "EXT_ARRAY %s\n" id
	| KNormal.t.ExtFunApp (id,args) -> Printf.printf "EXT_APP(%s" id;print_knormal_args args ();print_string ")\n"
	(*新しい*)
	| KNormal.t.Print id -> Printf.printf "PRINT(%s)\n" id
	| KNormal.t.Scan id -> Printf.printf "SCAN(%s)\n" id
	| KNormal.t.Mul (a,b) -> Printf.printf "MUL(%s,%s)\n" a b
	| KNormal.t.Div (a,b) -> Printf.printf "DIV(%s,%s)\n" a b
	| KNormal.t.Sqrt id -> Printf.printf "SQRT(%s)\n" id
	| _ -> print_string "nazo\n"
	;;

let print_knormal knormal =
	print_knormal_sub knormal 0;;

let iitostring idorimm = 
	match idorimm with
	| Asm.id_or_imm.V id -> id
	| Asm.id_or_imm.C c -> c.ToString();;

let rec print_assembly_sub asm depth () =
	tab_of_amount depth ();
	match asm with
	| Asm.Let ((id,tp),e,t) -> 
			Printf.printf "LET %s(%s) = \n" id (TypetoString tp); print_assembly_exp e (depth+1) (); print_assembly_sub t depth () 
	| Asm.Ans e -> Printf.printf "ANS:\n"; print_assembly_exp e (depth+1) ()
	| _ -> print_string "nazo\n"
and print_assembly_exp exp depth () =
	tab_of_amount depth ();
	match exp with
	| Asm.Nop -> print_string "NOP\n"
	| Asm.Li i -> Printf.printf "LI(%d)\n" i
	| Asm.FLi i -> Printf.printf "FLI(%d)\n" i
	| Asm.SetL (Id.L i) -> Printf.printf "SETL(%s)\n" i
	| Asm.Mr i -> Printf.printf "MR(%s)\n" i
	| Asm.Neg i -> Printf.printf "LI(%s)\n" i
	| Asm.Add (id,i) -> Printf.printf "ADD(%s + %s)\n" id (iitostring i)
	| Asm.Sub (id,i) -> Printf.printf "SUB(%s - %s)\n" id (iitostring i)
	| Asm.Mul (id,i) -> Printf.printf "MUL(%s * %s)\n" id (iitostring i)
	| Asm.Div (id,i) -> Printf.printf "DIV(%s / %s)\n" id (iitostring i)
	| Asm.Slw (id,i) -> Printf.printf "SLW(%s + %s)\n" id (iitostring i)
	| Asm.Lwz (id,i) -> Printf.printf "LWZ(%s + %s)\n" id (iitostring i)
	| Asm.Stw (id1,id2,i) -> Printf.printf "SLW(%s + %s + %s)\n" id1 id2 (iitostring i)
	| Asm.FMr i -> Printf.printf "FMR(%s)\n" i
	| Asm.FNeg id -> Printf.printf "FNEG(%s)\n" id
	| Asm.FAdd (id1,id2) -> Printf.printf "FADD(%s +. %s)\n" id1 id2
	| Asm.FSub (id1,id2) -> Printf.printf "FSUB(%s -. %s)\n" id1 id2
	| Asm.FMul (id1,id2) -> Printf.printf "FMUL(%s *. %s)\n" id1 id2
	| Asm.FDiv (id1,id2) -> Printf.printf "FDIV(%s /. %s)\n" id1 id2
	| Asm.Lfd (id1,ii) -> Printf.printf "LFD(%s %s)\n" id1 (iitostring ii)
	| Asm.Stfd (id1,id2,ii) -> Printf.printf "Stfd(%s %s %s)\n" id1 id2 (iitostring ii)
	| Asm.Comment str -> Printf.printf "Comment:%s\n" str
	| Asm.CallCls (ca,iarg,farg) -> Printf.printf "CallCls %s (IntArg:" ca; print_knormal_args iarg (); print_string "/FloatArg:"; print_knormal_args farg ();print_string ")\n"
	| Asm.CallDir (Id.L ca,iarg,farg) -> Printf.printf "CallCls %s (IntArg:" ca; print_knormal_args iarg (); print_string "/FloatArg:"; print_knormal_args farg ();print_string ")\n"
	| Asm.Save (id1,id2) -> Printf.printf "SAVE %s %s\n" id1 id2
	| Asm.Restore id1 -> Printf.printf "REST %s\n" id1
	| Asm.Print id -> Printf.printf "PRINT %s\n" id
	| Asm.Scan id -> Printf.printf "SCAN %s\n" id
	| _ -> print_string "nazo\n";;

let print_assembly asmprog = 
	match asmprog with
	| Asm.Prog (a,b,asm) -> print_assembly_sub asm 0;;

let rec print_closure_sub t depth () = 
	tab_of_amount depth ();	
	match t with
	| Closure.t.Unit -> print_string "Unit\n"
	| Closure.t.Int i -> Printf.printf "Int(%d)\n" i
	| Closure.t.Float f -> Printf.printf "Float(%f)\n" f
	| Closure.t.Neg n -> Printf.printf "Neg(%s)\n" n
	| Closure.t.Add (a,b) -> Printf.printf "Add(%s + %s)\n" a b
	| Closure.t.Sub (a,b) -> Printf.printf "Sub(%s - %s)\n" a b
	| Closure.t.Mul (a,b) -> Printf.printf "Mul(%s * %s)\n" a b
	| Closure.t.Div (a,b) -> Printf.printf "Div(%s * %s)\n" a b
	| Closure.t.FNeg a -> Printf.printf "FNeg(%s)\n" a
	| Closure.t.FAdd (a,b) -> Printf.printf "FAdd(%s + %s)\n" a b
	| Closure.t.FSub (a,b) -> Printf.printf "FSub(%s - %s)\n" a b
	| Closure.t.FMul (a,b) -> Printf.printf "FMul(%s * %s)\n" a b
	| Closure.t.FDiv (a,b) -> Printf.printf "FDiv(%s / %s)\n" a b
	| Closure.t.IfEq (a,b,e1,e2) -> Printf.printf "IF(%s=%s)\n" a b;print_closure_sub e1 (depth+1) (); print_closure_sub e2 (depth+1) ();
	| Closure.t.IfLE (a,b,e1,e2) -> Printf.printf "IF(%s<=%s)\n" a b;print_closure_sub e1 (depth+1) (); print_closure_sub e2 (depth+1) ();
	| Closure.t.Var id -> Printf.printf "VAR(%s)\n" id
	| Closure.t.Let ((id,tp),e1,e2) ->
			Printf.printf "Let %s(%s)\n" id (TypetoString tp);
			print_closure_sub e1 (depth+1) ();
			print_closure_sub e2 (depth+1) ()
	| Closure.t.MakeCls ((i,t),c,t2) -> 
			let {Closure.closure.entry = ent; Closure.closure.actual_fv = fv} = c in
			let (Id.L ents) = ent in
			Printf.printf "MakeCls %s(%s) %s" i (TypetoString t) ents;
			print_knormal_args fv ();
			print_string "\n";
			print_closure_sub t2 (depth+1) ()
	| Closure.t.AppCls (it,itl) -> 
			Printf.printf "AppCls %s" it; print_knormal_args itl ();print_string "\n"
	| Closure.t.AppDir ((Id.L it),itl) -> 
			Printf.printf "AppDir %s" it; print_knormal_args itl ();print_string "\n"
	| Closure.t.ExtArray (Id.L id) -> Printf.printf "EXT_ARRAY %s\n" id
	| Closure.t.Get (array,index) -> Printf.printf "Get %s[%s]\n" array index
	| Closure.t.Put (array,index,data) -> Printf.printf "Set %s[%s] := %s\n" array index data
	(*新しい*)
	| Closure.t.Print id -> Printf.printf "PRINT(%s)\n" id
	| Closure.t.Scan id -> Printf.printf "SCAN(%s)\n" id
	| _ -> print_string "nazo\n"

let print_fundef fundef ()= 
	let {Closure.fundef.name = n ; Closure.fundef.args = arg ; Closure.fundef.formal_fv = fv ; Closure.fundef.body = bd} = fundef in
	let (Id.L nid,nt) = n in
	Printf.printf "%s " nid;
	print_args arg ();
	print_args fv ();
	Printf.printf "%s\nbody:\n" (TypetoString nt);
	print_closure_sub bd 0 ();
	print_string "\n";;
	
let rec print_fundefs fl () = 
	match fl with
	| [] -> ()
	| x::xs -> print_fundef x ();print_fundefs xs ();;

let print_closure clsprog = 
	match clsprog with
	| Closure.Prog (fl,t) -> print_fundefs fl ();print_string "T:\n";print_closure_sub t 0;;

