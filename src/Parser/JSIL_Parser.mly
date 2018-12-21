%{
open CCommon
open SCommon
open SVal

(* Tables where we collect the predicates and the procedures as we parse them. *)
let predicate_table : (string, Pred.t) Hashtbl.t = Hashtbl.create 511
let procedure_table : (string, EProc.t) Hashtbl.t = Hashtbl.create 511
let only_spec_table : (string, Spec.t) Hashtbl.t = Hashtbl.create 511
let lemma_table : (string, Lemma.t) Hashtbl.t = Hashtbl.create 511
let procedure_names  : (string list) ref = ref []
let normalised_lvar_r = Str.regexp "##NORMALISED_LVAR"
let macro_table : (string, Macro.t) Hashtbl.t = Hashtbl.create 511
let bispecs_table : (string, BiSpec.t) Hashtbl.t = Hashtbl.create 511

let copy_and_clear_globals () =
  let lemm'    = Hashtbl.copy lemma_table in
  let pred'    = Hashtbl.copy predicate_table in
  let ospc'    = Hashtbl.copy only_spec_table in
  let proc'    = Hashtbl.copy procedure_table in
  let macro'   = Hashtbl.copy macro_table in
  let bispecs' = Hashtbl.copy bispecs_table in 
  let proc_names = !procedure_names in
  Hashtbl.clear lemma_table;
  Hashtbl.clear predicate_table;
  Hashtbl.clear procedure_table;
  Hashtbl.clear only_spec_table;
  Hashtbl.clear macro_table; 
  Hashtbl.clear bispecs_table; 
  procedure_names = ref [];
  (lemm', pred' , ospc', proc', proc_names, macro', bispecs')
%}

(***** Token definitions *****)
(*  JS Logic Literals *)
%token SCOPELEXPR
%token SCOPE
%token THIS
%token CLOSURE
%token SCSCOPE
%token OCHAINS
%token SCHAIN
%token UNDERSCORE
(* Permissions *)
%token READABLE  
%token MUTABLE    
%token DELETABLE  
(* Type literals *)
%token UNDEFTYPELIT
%token NULLTYPELIT
%token EMPTYTYPELIT
%token NONETYPELIT
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token LISTTYPELIT
%token TYPETYPELIT
%token SETTYPELIT
(* Constants *)
%token MIN_FLOAT
%token MAX_FLOAT
%token RANDOM
%token E
%token LN10
%token LN2
%token LOG2E
%token LOG10E
%token PI
%token SQRT1_2
%token SQRT2
%token UTCTIME
%token LOCALTIME
(* Literals *)
%token UNDEFINED
%token NULL
%token EMPTY
%token TRUE
%token FALSE
%token <float> FLOAT
%token NAN
%token INFINITY
%token <string> STRING
%token <string> LOC
%token LSTNIL
%token LSTOPEN
%token LSTCLOSE
(* PVariables *)
%token <string> VAR
(* Filenames *)
%token <string> FILENAME
(* Binary operators *)
%token EQUAL
%token LESSTHAN
%token GREATERTHAN
%token LESSTHANEQUAL
%token GREATERTHANEQUAL
%token LESSTHANSTRING
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token AND
%token OR
%token BITWISEAND
%token BITWISEOR
%token BITWISEXOR
%token LEFTSHIFT
%token SIGNEDRIGHTSHIFT
%token UNSIGNEDRIGHTSHIFT
%token M_ATAN2
%token M_POW
%token LSTCONS
%token LSTCAT
%token LSTREV
%token STRCAT
(* Unary operators *)
(* Unary minus uses the same token as binary minus: MINUS *)
%token NOT
%token BITWISENOT
%token M_ISNAN
%token M_ABS
%token M_ACOS
%token M_ASIN
%token M_ATAN
%token M_CEIL
%token M_COS
%token M_EXP
%token M_FLOOR
%token M_LOG
%token M_ROUND
%token M_SGN
%token M_SIN
%token M_SQRT
%token M_TAN
%token TOSTRING
%token TOINT
%token TOUINT16
%token TOINT32
%token TOUINT32
%token TONUMBER
%token CAR
%token CDR
%token SETTOLIST
%token LSTLEN
%token STRLEN
(* Expression keywords *)
%token TYPEOF
%token ASSUME
%token ASSERT
%token SEPASSERT
%token SEPAPPLY
%token INVARIANT
%token RNUMSYM
%token RSTRSYM
%token RBLNSYM
%token ASSUME_TYPE
%token SPEC_VAR
%token LSTNTH
%token STRNTH
%token BIND
%token EXISTENTIALS
%token BRANCH
%token USESUBST
(* Command keywords  *)
%token SKIP
%token DEFEQ
%token NEW
%token DELETE
%token DELETEOBJ
%token HASFIELD
%token GETFIELDS
%token METADATA
%token ARGUMENTS
%token GOTO
%token WITH
%token APPLY
%token PHI
%token RETURN
%token THROW
%token EXTERN
(* Logic variables *)
%token <string> LVAR
(* Logical expressions *)
%token LNONE
%token <string> ALOC
(* Logic assertions *)
%token OASSERT
%token CASSERT
%token LAND
%token LOR
%token LNOT
%token LTRUE
%token LFALSE
%token LEQUAL
%token LLESSTHAN
%token LLESSTHANEQUAL
%token LLESSTHANSTRING
%token LARROW
%token LEMP
%token EMPTYFIELDS
(*%token LEXISTS *)
%token LFORALL
%token LTYPES
%token LMETADATA
%token LEXTENSIBLE
(* Logic predicates *)
%token PURE
%token PRED
(* Logic commands *)
%token OLCMD
%token CLCMD
%token OOLCMD
%token CCLCMD
%token FOLD
%token UNFOLD
%token UNFOLDALL
%token FLASH
%token RECUNFOLD
%token CALLSPEC
%token LIF
%token LTHEN
%token LELSE
(* Procedure specification keywords *)
%token ONLY
%token SPEC
%token BISPEC
%token LEMMA
%token VARIANT
%token NORMAL
%token ERROR
(* JS only spec specifics *)
%token JSOS
%token JSOSPRE
%token JSOSPOST
%token JSOSOUT
(* Procedure definition keywords *)
%token PROC
(* Others *)
%token IMPORT
%token MACRO
(* Separators *)
%token DOT
%token COMMA
%token COLON
%token SCOLON
(*%token DOT*)
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token CLBRACKET
%token CRBRACKET
(* SETS *)
%token SETUNION
%token SETINTER
%token SETDIFF
%token SETMEM
%token SETSUB
%token LSETMEM
%token LSETSUB
%token SETOPEN
%token SETCLOSE
(* EOF *)
%token EOF

(***** Precedence of operators *****)
(* The later an operator is listed, the higher precedence it is given. *)
(* Logic operators have lower precedence *)
%nonassoc DOT
%left LOR
%left LAND
%left separating_conjunction
%right LNOT
%nonassoc LEQUAL LLESSTHAN LLESSTHANEQUAL LLESSTHANSTRING LARROW
%nonassoc SETMEM SETSUB LSETMEM LSETSUB
(* Program operators have higher precedence.*)
(* Based on JavaScript:
   https://developer.mozilla.org/en/docs/Web/JavaScript/Reference/Operators/Operator_Precedence *)
%left OR
%left AND
%left BITWISEOR
%left BITWISEXOR
%left BITWISEAND
%nonassoc EQUAL
%nonassoc LESSTHAN LESSTHANSTRING LESSTHANEQUAL
%left LEFTSHIFT SIGNEDRIGHTSHIFT UNSIGNEDRIGHTSHIFT
%left PLUS MINUS
%left TIMES DIV MOD M_POW
%left M_ATAN2 LSTCAT STRCAT SETDIFF

%nonassoc binop_prec
%nonassoc unop_prec 

%nonassoc FLOAT

(***** Types and entry points *****)
%type <Literal.t>    lit_target
%type <Type.t>       type_target
%type <Constant.t>   constant_target
%type <UnOp.t>       unop_target
%type <BinOp.t>      binop_target
%type <NOp.t>        nop_target
%type <JSAsrt.pt>    js_pure_assertion_target
%type <Formula.t>    pure_assertion_target

%type <EProg.t> main_target
%type <Pred.t list * Spec.t list> pred_spec_target
%type <JSPred.t> js_pred_target
%type <Asrt.t> top_level_assertion_target
%type <JSAsrt.t> top_level_js_assertion_target
%type <(string * string list) option * JSAsrt.t> top_level_js_pre_target
%type <JSAsrt.t list> top_level_js_assertion_list_target
%type <Lemma.t> jsil_lemma_target
%type <JSSpec.t> js_only_spec_target
%type <JSLCmd.t list> js_logic_cmds_target
%type <LabCmd.t> cmd_target
%type <Expr.t> top_level_expr_target

%start main_target
%start pred_spec_target
%start top_level_assertion_target
%start top_level_expr_target
%start top_level_js_pre_target
%start top_level_js_assertion_target
%start top_level_js_assertion_list_target
%start jsil_lemma_target
%start js_pred_target
%start js_only_spec_target
%start js_logic_cmds_target
%%

(********* JSIL *********)

main_target:
  | imports = option(import_target); proc_names = declaration_target; EOF
      {  
        let imports = Option.default [] imports in 
        let (lemm, pred, ospc, proc, _, macros, bispecs) = copy_and_clear_globals () in

        EProg.init imports lemm pred ospc proc macros bispecs (List.rev proc_names)
      }
;

declaration_target:
  | proc_names = declaration_target; jsil_lemma_target
    { proc_names }
  | jsil_lemma_target
    { [ ] }
  | proc_names = declaration_target; pred_target
    { proc_names }
  | pred_target
    { [ ] }
  | proc_names = declaration_target; proc_name = proc_target 
    { proc_name :: proc_names }
  | proc_name = proc_target
    { [ proc_name ] }
  | proc_names = declaration_target; macro_target
    { proc_names }
  | macro_target
    { [ ] }
  | proc_names = declaration_target; only_spec_target
    { proc_names }
  | only_spec_target
    { [ ] }
  | proc_names = declaration_target; bi_spec_target
    { proc_names }
  | bi_spec_target
    { [ ] }
;

import_target:
  IMPORT; imports = separated_nonempty_list(COMMA, FILENAME); SCOLON { imports }
;

(* [spec;] proc xpto (x, y) { cmd_list } with { ret: x, i; [err: x, j] }; *)
proc_target:
  spec = option(spec_target); proc_head = proc_head_target; CLBRACKET; cmd_list = cmd_list_target; CRBRACKET; SCOLON
    {
      let name, params = proc_head in

      let proc : EProc.t = {
        name; body = Array.of_list cmd_list; params; spec
      } in
      (* TODO: Warn if conflicting names? *)
      procedure_names :=  name :: (!procedure_names);
      Hashtbl.replace procedure_table name proc;
      name 
    }
;

proc_head_target:
  PROC; proc_name = VAR; LBRACE; param_list = separated_list(COMMA, VAR); RBRACE
  { 
    (proc_name, param_list)
  }
;

cmd_list_target:
  cmd_list = separated_nonempty_list(SCOLON, cmd_with_label)
    {
      List.map
        (fun (lab, cmd) ->
          let annot : Annot.t = Annot.init () in 
          annot, lab, cmd)
    cmd_list
  }
;

cmd_with_label:
  | cmd = cmd_target
    { None, cmd }
  | lab = VAR; COLON; cmd = cmd_target
  { Some lab, cmd }
;


permission_target: 
(* r *)
  | READABLE   { None }
  | MUTABLE    { None }
  | DELETABLE  { None }
; 


ass_permission_target: 
(*<p>*)
  | LESSTHAN; p=permission_target; GREATERTHAN 
    { p }
;

lvar_le_pair_target: 
  lv = LVAR; COLON; e=expr_target { (lv, e )}
; 

use_subst_target: 
  | USESUBST; LBRACKET; lab=VAR; MINUS; subst = separated_list(COMMA, lvar_le_pair_target); RBRACKET
      { (lab, subst) }
  | USESUBST; LBRACKET; lab=VAR RBRACKET
      { (lab, []) }
;

cmd_target:
(*** Basic commands ***)
(* skip *)
  | SKIP
    { LBasic (Skip) }
(* x := e *)
  | v=VAR; DEFEQ; e=expr_target
    { LBasic (Assignment (v, e)) }
(* x := new(metadata) *)
  | v=VAR; DEFEQ; NEW; LBRACE; arg_a=option(expr_target); arg_b=option(expr_target); RBRACE
    { 
      let loc, metadata = (match arg_a, arg_b with 
      | Some _, None -> None, arg_a
      | None, Some _ -> raise (Failure "Parser: This cannot happen")
      | _, _ -> arg_a, arg_b
      ) in
        LBasic (New (v, loc, metadata)) 
    }
(* x := [e1, e2] *)
  | v=VAR; DEFEQ; LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET
    { LBasic (Lookup (v, e1, e2)) }
(* [e1, e2] := <p> e3 *)
  | LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET; DEFEQ; op=option(ass_permission_target); e3=expr_target
    { LBasic (Mutation (e1, e2, e3)) }
(* delete(e1, e2) *)
  | DELETE; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
    { LBasic (Delete (e1, e2)) }
(* deleteObject(e1) *)
  | DELETEOBJ; LBRACE; e1=expr_target; RBRACE
    { LBasic (DeleteObj (e1)) }
(* x := hasField(e1, e2) *)
  | v=VAR; DEFEQ; HASFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
    { LBasic (HasField (v, e1, e2)) }
(* x := getFields (e1) *)
  | v = VAR; DEFEQ; GETFIELDS; LBRACE; e=expr_target; RBRACE
    { LBasic (GetFields (v, e)) }
(* x := metadata (e) *)
  | v = VAR; DEFEQ; METADATA; LBRACE; e=expr_target; RBRACE
    { LBasic (MetaData (v, e)) }
(*** Other commands ***)
(* goto i *)
  | GOTO; i=VAR
    { LGoto i }
(* goto [e] i j *)
  | GOTO LBRACKET; e=expr_target; RBRACKET; i=VAR; j=VAR
    { LGuardedGoto (e, i, j) }
(* x := e(e1, ..., en) with j use_subst [bla - #x: bla, #y: ble] *)
  | v=VAR; DEFEQ; e=expr_target;
    LBRACE; es=separated_list(COMMA, expr_target); RBRACE; oi = option(call_with_target); subst = option(use_subst_target)
    { 
      LCall (v, e, es, oi, subst) 
    }

(* x := e(e1, ..., en) with j *)
  | v=VAR; DEFEQ; EXTERN; pname=VAR;
    LBRACE; es=separated_list(COMMA, expr_target); RBRACE; oi = option(call_with_target)
    { LECall (v, PVar pname, es, oi) }

(* x := apply (e1, ..., en) with j *)
  | v=VAR; DEFEQ; APPLY;
    LBRACE; es=expr_target; RBRACE; oi = option(call_with_target)
    { LApply (v, es, oi) }
(* x := args *)
  | v = VAR; DEFEQ; ARGUMENTS
    { (LArguments v) }
(* x := PHI(e1, e2, ... en); *)
  | PHI; LBRACE; phi_args =separated_list(SCOLON, phi_target); RBRACE
    { 
      match phi_args with 
      | [] -> raise (Failure "EMPTY PHI")
      | _  -> LPhiAssignment phi_args
    }
(* return *)
  | RETURN { LReturnNormal }
  | THROW  { LReturnError  }
(* Logic command *)
  | lcmd = logic_cmd_target 
    { LLogic lcmd }
;

phi_target: 
  v = VAR; COLON; args = separated_list(COMMA, expr_target) 
    {
      (v, args)
    }



call_with_target:
  WITH; i=VAR { i }
;

expr_target:
(* literal *)
  | lit=lit_target { Lit lit }
(* None *)
  | LNONE
    { Nono }
(* Logic variable *)
  | lvar = logic_variable_target
    { lvar }
(* Abstract locations are *normally* computed on normalisation *)
  | ALOC
    { ALoc $1 }
(* Program variable (including the special variable "ret") *)
  | pvar = program_variable_target
    { pvar }
(* e binop e *)
  | e1=expr_target; bop=binop_target; e2=expr_target
     { BinOp (e1, bop, e2) } %prec binop_prec
    | e1=expr_target; bop=GREATERTHAN; e2=expr_target
       { BinOp (e2, LessThan, e1) }
    | e1=expr_target; bop=GREATERTHANEQUAL; e2=expr_target
       { BinOp (e2, LessThanEqual, e1) }
(* unop e *)
    | uop=unop_target; e=expr_target
     { UnOp (uop, e) } %prec unop_prec
(* - e *)
(* Unary negation has the same precedence as logical not, not as binary negation. *)
  | MINUS; e=expr_target
     { UnOp (UnaryMinus, e) } %prec unop_prec
(* {{ e, ..., e }} *)
  | LSTOPEN; exprlist = separated_nonempty_list(COMMA, expr_target); LSTCLOSE
     { EList exprlist }
(* -{- e, ..., e -}- *)
  | SETOPEN; exprlist = separated_list(COMMA, expr_target); SETCLOSE
     { ESet (Expr.Set.elements (Expr.Set.of_list exprlist)) }
(* l-nth (list, n) *)
  | LSTNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
     { BinOp (e1, LstNth, e2) }
(* nop le *)
  | nop=nop_target; LBRACE; les=separated_list(COMMA, expr_target); RBRACE
     { 
        let les = 
          match (nop : NOp.t) with 
        | SetInter
          | SetUnion -> Expr.Set.elements (Expr.Set.of_list les)
          | _ -> les in 
        NOp (nop, les) 
     }
(* s-nth (string, n) *)
  | STRNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
     { BinOp (e1, StrNth, e2) }
(* (e) *)
    | LBRACE; e=expr_target; RBRACE
    { e }
(* Ignore variable *)
  | UNDERSCORE
    { LVar (fresh_lvar ()) }
;

top_level_expr_target:
  e = expr_target; EOF { e }
;

(********* LOGIC *********)

(* pred name (arg1, ..., argn) : def1, ..., defn ; *)
pred_target:
  p = option(PURE); PRED; pred_head = pred_head_target; COLON;
  definitions = separated_nonempty_list(COMMA, named_assertion_target); SCOLON
  {
    let pure = match p with | Some _ -> true | None -> false in 
    let (name, num_params, params, ins) = pred_head in
    let normalised = !previously_normalised in
  let pred : Pred.t = { name; num_params; params; ins; definitions; pure; normalised } in
  Hashtbl.add predicate_table name pred;
  pred
  }
;

named_assertion_target:
  id = option(assertion_id_target); a = assertion_target
  { (id, a) }
;

(* 
  [def1_id: #x1, #x2, #x3 ] 
  [def1_id]
*)
assertion_id_target: 
  | LBRACKET; v=VAR; RBRACKET
      { (v, []) }
  | LBRACKET; v=VAR; COLON; lvars=separated_nonempty_list(COMMA, LVAR); RBRACKET
      { (v, lvars) }
;

js_named_assertion_target:
  id = option(assertion_id_target); a = js_assertion_target
  { (id, a) }
;

js_pred_target:
(* pred name (arg1, ..., argn) : [def1_id: x1, ...] def1, ..., [def1_id: x1, ...] defn ; *)
  pure = option(PURE); PRED; pred_head = js_pred_head_target; COLON;
  definitions = separated_nonempty_list(COMMA, js_named_assertion_target); SCOLON
    { (* Add the predicate to the collection *)
      let (name, num_params, params, ins) = pred_head in
      let pure = match pure with | Some _ -> true | None -> false in 
      let pred : JSPred.t = { name; num_params; params; ins; definitions; pure } in
      pred
    }
;



pred_head_target:
  name = VAR; LBRACE; params = separated_list(COMMA, pred_param_target); RBRACE;
  { (* Register the predicate declaration in the syntax checker *)
    let num_params = List.length params in
    let params, ins = List.split params in
    let param_names, _ = List.split params in
    let ins = List.map Option.get (List.filter (fun x -> x <> None) (List.mapi (fun i is_in -> if is_in then Some i else None) ins)) in
    let ins = if (List.length ins > 0) then ins else (List.mapi (fun i _ -> i) param_names) in 
    (* register_predicate name num_params; *)
    (* enter_predicate params; *)
    (name, num_params, params, ins)
  }
;


js_pred_head_target:
  name = VAR; LBRACE; params = separated_list(COMMA, js_pred_param_target); RBRACE;
  { (* Register the predicate declaration in the syntax checker *)
    let num_params = List.length params in
    let params, ins = List.split params in
    let param_names, _ = List.split params in
    let ins = List.map Option.get (List.filter (fun x -> x <> None) (List.mapi (fun i is_in -> if is_in then Some i else None) ins)) in
    let ins = if (List.length ins > 0) then ins else (List.mapi (fun i _ -> i) param_names) in 
    (name, num_params, params, ins)
  }
;

pred_param_target:
  (* Program variable with in-parameter status and optional type *)
  | in_param = option(PLUS); v = VAR; t = option(preceded(COLON, type_target))
    { let in_param = Option.map_default (fun _ -> true) false in_param in
      (v, t), in_param }
;


js_pred_param_target:
  (* Program variable with optional type *)
  | in_param = option(PLUS); v = VAR; t = option(preceded(COLON, type_target))
    { let in_param = Option.map_default (fun _ -> true) false in_param in
      (v, t), in_param }
;


pre_logic_cmd_target:
(* [* logic_cmds *] *)
  | OLCMD; logic_cmds = separated_list(SCOLON, logic_cmd_target); CLCMD
    { logic_cmds }

post_logic_cmd_target:
(* [+ logic_cmds +] *)
  | OOLCMD; logic_cmds = separated_list(SCOLON, logic_cmd_target); CCLCMD
    { logic_cmds }

var_and_le_target:
  | LBRACE; lvar = LVAR; DEFEQ; le = expr_target; RBRACE;
    { (lvar, le) }
;

(* [ def with #x := le1 and ... ] *)
unfold_info_target:
  | LBRACKET; id = VAR; WITH; var_les = separated_list(AND, var_and_le_target); RBRACKET
    { (id, var_les) }
;


binders_target: 
  | LBRACKET; BIND; COLON; xs = separated_list(COMMA, LVAR); RBRACKET
    { xs }
;

existentials_target: 
  | LBRACKET; EXISTENTIALS; COLON; xs = separated_list(COMMA, LVAR); RBRACKET
    { xs }
;


(* TODO: Check that the assertions are only predicates, or deal with full assertions in the execution *)
logic_cmd_target:
(* fold x(e1, ..., en) *)
  | FOLD; name = VAR; LBRACE; les=separated_list(COMMA, expr_target); RBRACE; fold_info = option(unfold_info_target) 
    { SL (Fold (name, les, fold_info)) }

(* unfold x(e1, ..., en) [ def with #x := le1 and ... ] *)
  | UNFOLD; name = VAR; LBRACE; les=separated_list(COMMA, expr_target); RBRACE; unfold_info = option(unfold_info_target)
    { SL (Unfold (name, les, unfold_info, false)) }

(* unfold* x(e1, ..., en) [ def with #x := le1 and ... ] *)
  | RECUNFOLD; name = VAR; LBRACE; les=separated_list(COMMA, expr_target); RBRACE; unfold_info = option(unfold_info_target)
    { SL (Unfold (name, les, unfold_info, true)) }

(* unfold_all x *)
  | UNFOLDALL; name = VAR
    { SL (GUnfold name) }

(* invariant (a) [existentials: x, y, z] *)
  | INVARIANT; LBRACE; a = assertion_target; RBRACE; existentials = option(existentials_target)
    { SL (Invariant (a, Option.default [ ] existentials)) }

(* apply lemma_name(args) [bind: x, y ] *)
   | SEPAPPLY; lemma_name = VAR; LBRACE; params = separated_list(COMMA, expr_target); RBRACE; binders = option(binders_target)
    { 
      let binders = Option.default [] binders in 
      SL (ApplyLem (lemma_name, params, binders)) 
    }

(* assert_* (a) [bind: x, y, z] *)
  | SEPASSERT; LBRACE; a = assertion_target; RBRACE; binders = option(binders_target)
    { SL (SepAssert (a, Option.default [ ] binders)) }

(* if(le) { lcmd* } else { lcmd* } *)
  | LIF; LBRACE; le=expr_target; RBRACE; LTHEN; CLBRACKET;
      then_lcmds = separated_list(SCOLON, logic_cmd_target);
      CRBRACKET; LELSE; CLBRACKET;
      else_lcmds = separated_list(SCOLON, logic_cmd_target);
       CRBRACKET;
    { If (le, then_lcmds, else_lcmds)}

(* if(e) { lcmd* } *)
  | LIF; LBRACE; le=expr_target; RBRACE; LTHEN; CLBRACKET;
      then_lcmds = separated_list(SCOLON, logic_cmd_target);
      CRBRACKET;
    { If (le, then_lcmds, [])}

  | macro = macro_head_target;
    { let (name, params) = macro in Macro (name, params) }

(* assert (a) *)
  | ASSERT; LBRACE; a = pure_assertion_target; RBRACE
    { Assert a }

(* assume (a) *)
  | ASSUME; LBRACE; a = pure_assertion_target; RBRACE
    { Assume a }

(* assume_type (x, t) *)
  | ASSUME_TYPE; LBRACE; x=LVAR; COMMA; t=type_target; RBRACE
    { AssumeType (x, t) }

(* spec_var (x, t) *)
  | SPEC_VAR; LBRACE; xs = separated_list(COMMA, LVAR); RBRACE
    { SpecVar xs }

(* branch (fo) *)
  | BRANCH; LBRACE; fo = pure_assertion_target; RBRACE   
     { Branch fo }
;


macro_target:
  MACRO; head = macro_head_def_target; COLON; lcmds = separated_list(SCOLON, logic_cmd_target)
  { let (name, params) = head in 
    let macro = { Macro.name = name; Macro.params = params; Macro.definition = lcmds } in
    Hashtbl.add macro_table macro.name macro }

macro_head_def_target:
 | name = VAR; LBRACE; params = separated_list(COMMA, VAR); RBRACE
   { (name, params) }

macro_head_target:
 | name = VAR; LBRACE; params = separated_list(COMMA, expr_target); RBRACE
   { (name, params) }

only_spec_target:
(* only spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
  ONLY; SPEC; head = spec_head_target;
  sspecs = separated_nonempty_list(SCOLON, pre_post_target);
  { let (name, params) = head in
    let normalised = !previously_normalised in
    let spec : Spec.t = { name; params; sspecs; normalised; to_verify = true } in
    Hashtbl.replace only_spec_table name spec;
  }

js_only_spec_target:
(* js_only_spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
  JSOS; spec_head = spec_head_target;
  sspecs = separated_nonempty_list(SCOLON, js_pre_post_target); EOF
  {
    let (name, params) = spec_head in
    { name; params; sspecs  }
  }

jsil_lemma_target:
  (* lemma xpto (x, y)
     variant(x)
     [[ pre ]]
     [[ post ]] [existentials: a, b, c]
     [* proof_body *] *)
  LEMMA; lemma_head = jsil_lemma_head_target; variant = option(jsil_lemma_variant_target);
    pre = spec_line; posts = mult_spec_line; existentials=option(existentials_target); proof = option(jsil_lemma_proof_target);
  {
      let (name, params) = lemma_head in
      let existentials = Option.default [] existentials in 
      let lemma : Lemma.t = { name; params; pre; posts; variant; proof; existentials} in
      Hashtbl.replace lemma_table name lemma;
      lemma
  }

jsil_lemma_head_target:
  lemma_name = VAR; LBRACE; lemma_params = separated_list(COMMA, VAR); RBRACE
  {
    (lemma_name, lemma_params)
  }
;

jsil_lemma_variant_target:
  VARIANT LBRACE; variant = expr_target; RBRACE
  {
    variant
  }
;

jsil_lemma_proof_target:
  OLCMD; proof = separated_list(SCOLON, logic_cmd_target); CLCMD;
  { proof }

js_pre_post_target:
(* [lab: #x1, ..., #xn] [[ a1 ]] [[ a1'; ...; an' ]] flag *)
  lab_spec = option(lab_spec_target);
  OASSERT; pre  = js_assertion_target; CASSERT;
  OASSERT; post = separated_list(SCOLON, js_assertion_target); CASSERT;
  flag = outcome_target;
  { let sspec : JSSpec.st = { pre; post; flag; label = lab_spec } in sspec }
;

outcome_target:
  | NORMAL { Flag.Normal }
  | ERROR  { Flag.Error  }

spec_target:
(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
  SPEC; spec_head = spec_head_target;
  proc_specs = separated_nonempty_list(SCOLON, pre_post_target)
  { let (name, params) = spec_head in
    let is_normalised = !previously_normalised in
    { Spec.name = name; Spec.params = params; Spec.sspecs = proc_specs; Spec.normalised = is_normalised; Spec.to_verify = true }
  }
;

bi_spec_target:
(* bispec xpto (x, y) : [[ assertion ]] *)
  BISPEC; spec_head = spec_head_target; COLON; asrt = spec_line
  { 
    let (name, params) = spec_head in
    let is_normalised = !previously_normalised in
    let bi_spec : BiSpec.t = 
      {
        name       = name; 
        params     = params;
        pre        = asrt; 
        normalised = is_normalised  
      } in 
    Hashtbl.replace bispecs_table name bi_spec     
  }
;


(* <spec_name: #bla, #ble, #bli> *)
lab_spec_target: 
  | LESSTHAN; sspec_name = VAR; COLON; lvars = separated_list (COMMA, LVAR); GREATERTHAN
    { (sspec_name, lvars) }
  | LESSTHAN; sspec_name = VAR; GREATERTHAN 
    { (sspec_name, []) }
; 

spec_head_target:
  spec_name = VAR; LBRACE; spec_params = separated_list(COMMA, VAR); RBRACE
  { (* enter_specs spec_params; *)
    (spec_name, spec_params)
  }
;

pre_post_target:
(* [spec_name: #bla, #ble, #bli] [[ .... ]] [[ .... ]] Normal *)
  | lab_spec = option(lab_spec_target); pre = spec_line; posts = mult_spec_line; NORMAL
    { 
    let spec : Spec.st = { pre; posts; flag = Normal; to_verify = true; label = lab_spec } in 
    spec 
    }
(* [[ .... ]] [[ .... ]] Error *)
  | lab_spec = option(lab_spec_target); pre = spec_line; posts = mult_spec_line; ERROR
  { 
    let spec : Spec.st = { pre; posts; flag = Error; to_verify = true; label = lab_spec} in 
    spec
  }
;

spec_line:
  OASSERT; assertion = assertion_target; CASSERT { assertion }
;

mult_spec_line:
  OASSERT; assertions = separated_list(SCOLON, assertion_target); CASSERT { assertions }
;



top_level_assertion_target:
  a = assertion_target; EOF { a }

assertion_target:
(* P * Q *)
(* The precedence of the separating conjunction is not the same as the arithmetic product *)
  | left_ass=assertion_target; TIMES; right_ass=assertion_target
    { Star (left_ass, right_ass) } %prec separating_conjunction
(* (E, E) -> E *)
  | LBRACE; obj_expr=expr_target; COMMA; prop_expr=expr_target; RBRACE; LARROW; perm = option(permission_target); val_expr=expr_target
    { PointsTo (obj_expr, prop_expr, val_expr) }
(* Metadata (eo, em) *)
  | LMETADATA; LBRACE; eo = expr_target; COMMA; em = expr_target; RBRACE
    { (* validate_pred_assertion (name, params); *)
      MetaData (eo, em)
    }
(* emp *)
  | LEMP;
    { Emp }
(* x(e1, ..., en) *)
  | name = VAR; LBRACE; params = separated_list(COMMA, expr_target); RBRACE
    { (* validate_pred_assertion (name, params); *)
      Pred (name, params)
    }
(* types (type_pairs) *)
  | LTYPES; LBRACE; type_pairs = separated_list(COMMA, type_env_pair_target); RBRACE
    { Types type_pairs }
(* empty_fields (le1 : le2) *)
  | EMPTYFIELDS; LBRACE; le=expr_target; COLON; domain=expr_target; RBRACE
    { EmptyFields (le, domain) }
(* (P) *)
  | LBRACE; ass=assertion_target; RBRACE
    { ass }
(* pure *)
  | f = pure_assertion_target
    { Pure f }
;


pure_assertion_target:
(* P /\ Q *)
  | left_ass=pure_assertion_target; LAND; right_ass=pure_assertion_target
    { And (left_ass, right_ass) }
(* P \/ Q *)
  | left_ass=pure_assertion_target; LOR; right_ass=pure_assertion_target
    { Or (left_ass, right_ass) }
(* ! Q *)
  | LNOT; ass=pure_assertion_target
    { Not (ass) }
(* true *)
  | LTRUE
    { True }
(* false *)
  | LFALSE
    { False }
(* E == E *)
  | left_expr=expr_target; LEQUAL; right_expr=expr_target
    { Eq (left_expr, right_expr) }
(* E <# E *)
  | left_expr=expr_target; LLESSTHAN; right_expr=expr_target
    { Less (left_expr, right_expr) }
(* E <=# E *)
  | left_expr=expr_target; LLESSTHANEQUAL; right_expr=expr_target
    { LessEq (left_expr, right_expr) }
(* E <s# E *)
  | left_expr=expr_target; LLESSTHANSTRING; right_expr=expr_target
    { StrLess (left_expr, right_expr) }
(* E --e-- E *)
  | left_expr=expr_target; LSETMEM; right_expr=expr_target
    { SetMem (left_expr, right_expr) }
(* E --s-- E *)
  | left_expr=expr_target; LSETSUB; right_expr=expr_target
    { SetSub (left_expr, right_expr) }
(* forall X, Y, Z . P *)
  | LFORALL; vars = separated_nonempty_list(COMMA, lvar_type_target); DOT; ass = pure_assertion_target
    { ForAll (vars, ass) }
(* (P) *)
  | LBRACE; f=pure_assertion_target; RBRACE
    { f }
; 



lvar_type_target:
  | lvar = just_logic_variable_target; COLON; the_type = type_target
    { (lvar, Some the_type) }
  | lvar = just_logic_variable_target;
    { (lvar, None) }



type_env_pair_target:
  | lvar = logic_variable_target; COLON; the_type=type_target
    { (lvar, the_type) }
  | pvar = program_variable_target; COLON; the_type=type_target
    { (pvar, the_type) }
;

logic_variable_target:
  v = LVAR
  {
    let v_imported = Str.replace_first normalised_lvar_r "_lvar_n" v in
    (* Prefixed with _n_ to avoid clashes *)
    LVar v_imported }
;

just_logic_variable_target:
  v = LVAR
  { (* validate_lvar v; *) v }

program_variable_target:
  | v = VAR
    { (* let _ = validate_pvar v in *) Expr.PVar v }
;

(********* PREDS and SPECS only *********)

pred_spec_target: preds = separated_list(AND, pred_target); specs = separated_list(AND, spec_target); EOF
  { preds, specs }

(********* COMMON *********)

lit_target:
  | UNDEFINED                 { Undefined }
  | NULL                      { Null }
  | EMPTY                     { Empty }
  | constant_target           { Constant $1 }
  | TRUE                      { Bool true }
  | FALSE                     { Bool false }
  | FLOAT                     { Num $1 }
  | NAN                       { Num nan }
  | INFINITY                  { Num infinity }
  | STRING                    { String $1 }
  | LOC                       { Loc $1 }
  | type_target               { Type $1 }
  | LSTNIL                    { LList [] }
  | LSTOPEN LSTCLOSE          { LList [] }
;

extensible_target:
  | TRUE                      { None }
  | FALSE                     { None }

nop_target:
  | SETUNION { NOp.SetUnion }
  | SETINTER { NOp.SetInter }
;

binop_target:
  | EQUAL              { Equal }
  | LESSTHAN           { LessThan }
  | LESSTHANEQUAL      { LessThanEqual }
  | LESSTHANSTRING     { LessThanString }
  | PLUS               { Plus }
  | MINUS              { Minus }
  | TIMES              { Times }
  | DIV                { Div }
  | MOD                { Mod }
  | AND                { And }
  | OR                 { Or }
  | BITWISEAND         { BitwiseAnd }
  | BITWISEOR          { BitwiseOr}
  | BITWISEXOR         { BitwiseXor }
  | LEFTSHIFT          { LeftShift }
  | SIGNEDRIGHTSHIFT   { SignedRightShift }
  | UNSIGNEDRIGHTSHIFT { UnsignedRightShift }
  | M_ATAN2            { M_atan2 }
  | M_POW              { M_pow }
  | LSTCONS            { LstCons }
  | LSTCAT             { LstCat }
  | STRCAT             { StrCat }
  | SETDIFF            { SetDiff }
  | SETMEM             { SetMem }
  | SETSUB             { SetSub }
;

unop_target:
  (* Unary minus defined in (l)expr_target *)
  | NOT         { Not }
  | BITWISENOT  { BitwiseNot }
  | M_ISNAN     { M_isNaN }
  | M_ABS       { M_abs }
  | M_ACOS      { M_acos }
  | M_ASIN      { M_asin }
  | M_ATAN      { M_atan }
  | M_CEIL      { M_ceil }
  | M_COS       { M_cos }
  | M_EXP       { M_exp }
  | M_FLOOR     { M_floor }
  | M_LOG       { M_log }
  | M_ROUND     { M_round }
  | M_SGN       { M_sgn }
  | M_SIN       { M_sin }
  | M_SQRT      { M_sqrt }
  | M_TAN       { M_tan }
  | TOSTRING    { ToStringOp }
  | TOINT       { ToIntOp }
  | TOUINT16    { ToUint16Op }
  | TOINT32     { ToInt32Op }
  | TOUINT32    { ToUint32Op }
  | TONUMBER    { ToNumberOp }
  | TYPEOF      { TypeOf }
  | CAR         { Car }
  | CDR         { Cdr }
  | LSTLEN      { LstLen }
  | LSTREV      { LstRev }
  | STRLEN      { StrLen }
  | SETTOLIST   { SetToList }
;

constant_target:
  | MIN_FLOAT { Min_float }
  | MAX_FLOAT { Max_float }
  | RANDOM    { Random }
  | E         { E }
  | LN10      { Ln10 }
  | LN2       { Ln2 }
  | LOG2E     { Log2e }
  | LOG10E    { Log10e }
  | PI        { Pi }
  | SQRT1_2   { Sqrt1_2 }
  | SQRT2     { Sqrt2 }
  | UTCTIME   { UTCTime }
  | LOCALTIME { LocalTime }
;

type_target:
  | UNDEFTYPELIT { UndefinedType }
  | NULLTYPELIT  { NullType }
  | EMPTYTYPELIT { EmptyType }
  | NONETYPELIT  { NoneType }
  | BOOLTYPELIT  { BooleanType }
  | NUMTYPELIT   { NumberType }
  | STRTYPELIT   { StringType }
  | OBJTYPELIT   { ObjectType }
  | LISTTYPELIT  { ListType }
  | TYPETYPELIT  { TypeType }
  | SETTYPELIT   { SetType }
;



(** JS Assertions - Copy Paste for YOUR LIFE **)
top_level_js_assertion_target:
  a = js_assertion_target; EOF { a }


js_sspec_existentials_target: COLON; existentials=separated_list(COMMA, LVAR)
  { existentials }

js_sspec_lab_target: 
  LBRACKET; lab=VAR; existentials = option(js_sspec_existentials_target); RBRACKET 
    { 
      match existentials with 
        | None -> (lab, [])
        | Some existentials -> (lab, existentials)
    } 
; 

top_level_js_pre_target:
  lab = option(js_sspec_lab_target); a=js_assertion_target; EOF { (lab, a) }
;

top_level_js_assertion_list_target:
  al = separated_list(SCOLON, js_assertion_target); EOF { al }

js_assertion_target:
(* Pure *)
  | f = js_pure_assertion_target 
    { Pure f }
(* P * Q *)
(* The precedence of the separating conjunction is not the same as the arithmetic product *)
  | left_ass=js_assertion_target; TIMES; right_ass=js_assertion_target
    { Star (left_ass, right_ass) } %prec separating_conjunction
(* (E, E) -> E *)
  | LBRACE; obj_expr=js_lexpr_target; COMMA; prop_expr=js_lexpr_target; RBRACE; LARROW; perm = option(permission_target); val_expr=js_lexpr_target
    { PointsTo (obj_expr, prop_expr, val_expr) }
(* emp *)
  | LEMP;
    { Emp }
(* schain(fid: le) *)
  | SCHAIN; LBRACE; fid=VAR; COLON; le=js_lexpr_target; RBRACE
    { SChain (fid, le) }
(* x(e1, ..., en) *)
  | name = VAR; LBRACE; params = separated_list(COMMA, js_lexpr_target); RBRACE
    {
      (* validate_pred_assertion (name, params); *)
      Pred (name, params)
    }
(* types (type_pairs) *)
  | LTYPES; LBRACE; type_pairs = separated_list(COMMA, js_type_env_pair_target); RBRACE
    { Types type_pairs }
(* scope(x: le) *)
  | SCOPE; LBRACE; v=VAR; COLON; le=js_lexpr_target; RBRACE
    { Scope (v, le) }
(* closure(x_0: le_0, ..., x_n: le_n; fid_0: le_0', ..., fid_n: le_n') *)
  | CLOSURE; LBRACE; var_les=separated_list(COMMA, var_js_le_pair_target); SCOLON; fid_scs=separated_list(COMMA, var_js_le_pair_target); RBRACE
    { Closure (var_les, fid_scs)  }
(* sc_scope(pid, x: le1, le2) *)
  | SCSCOPE; LBRACE; pid=VAR; COMMA; x=VAR; COLON; le1=js_lexpr_target; COMMA; le2=js_lexpr_target; RBRACE
    { VarSChain (pid, x, le1, le2) }
(* o_chains(pid1: le1, pid2: le2) *)
  | OCHAINS; LBRACE; pid1=VAR; COLON; le1=js_lexpr_target; COMMA; pid2=VAR; COLON; le2=js_lexpr_target; RBRACE
    { OSChains (pid1, le1, pid2, le2) }
(* empty_fields (le : le_domain) *)
  | EMPTYFIELDS; LBRACE; le=js_lexpr_target; COLON; domain=js_lexpr_target; RBRACE
    { EmptyFields (le, domain) }
(* Metadata (eo, em) *)
  | LMETADATA; LBRACE; eo = js_lexpr_target; em = js_lexpr_target; RBRACE
    { (* validate_pred_assertion (name, params); *)
      MetaData (eo, em)
    }
(* (P) *)
  | LBRACE; ass=js_assertion_target; RBRACE
    { ass }
;


js_lvar_type_target:
  | lvar = just_logic_variable_target; COLON; the_type = type_target
    { (lvar, the_type) }

js_pure_assertion_target: 
(* P /\ Q *)
  | left_ass=js_pure_assertion_target; LAND; right_ass=js_pure_assertion_target
    { And (left_ass, right_ass) }
(* P \/ Q *)
  | left_ass=js_pure_assertion_target; LOR; right_ass=js_pure_assertion_target
    { Or (left_ass, right_ass) }
(* ! Q *)
  | LNOT; ass=js_pure_assertion_target
    { Not (ass) }
(* true *)
  | LTRUE
    { True }
(* false *)
  | LFALSE
    { False }
(* E == E *)
  | left_expr=js_lexpr_target; LEQUAL; right_expr=js_lexpr_target
    { Eq (left_expr, right_expr) }
(* E <# E *)
  | left_expr=js_lexpr_target; LLESSTHAN; right_expr=js_lexpr_target
    { Less (left_expr, right_expr) }
(* E <=# E *)
  | left_expr=js_lexpr_target; LLESSTHANEQUAL; right_expr=js_lexpr_target
    { LessEq (left_expr, right_expr) }
(* E <s# E *)
  | left_expr=js_lexpr_target; LLESSTHANSTRING; right_expr=js_lexpr_target
    { StrLess (left_expr, right_expr) }
(* E --e-- E *)
  | left_expr=js_lexpr_target; LSETMEM; right_expr=js_lexpr_target
    { SetMem (left_expr, right_expr) }
(* E --s-- E *)
  | left_expr=js_lexpr_target; LSETSUB; right_expr=js_lexpr_target
    { SetSub (left_expr, right_expr) }
(* forall X, Y, Z . P *)
  | LFORALL; vars = separated_nonempty_list(COMMA, js_lvar_type_target); DOT; ass = js_pure_assertion_target
    { ForAll (vars, ass) }
(* (P) *)
  | LBRACE; f=js_pure_assertion_target; RBRACE
    { f }
; 


var_js_le_pair_target:
  v=VAR; COLON; le=js_lexpr_target { (v, le) }

js_lvar_le_pair_target: 
  lv = LVAR; COLON; le=js_lexpr_target { (lv, le )}


js_lexpr_preceded_by_comma_target:
  COMMA; le=js_lexpr_target { le }
;

js_program_variable_target:
  | v = VAR
    { (* let _ = validate_pvar v in *) v }
;

js_lexpr_target:
(* Logic literal *)
  | lit = lit_target
    { Lit lit }
(* None *)
  | LNONE
    { Nono }
(* program variable *)
  | pvar = js_program_variable_target
    { PVar pvar }
(* Logic variable *)
  | lvar = LVAR
    { LVar lvar }
(* e binop e *)
  | e1=js_lexpr_target; bop=binop_target; e2=js_lexpr_target
    { BinOp (e1, bop, e2) } %prec binop_prec
(* unop e *)
  | uop=unop_target; e=js_lexpr_target
    { UnOp (uop, e) } %prec unop_prec
(* nop (le1, ..., len) *)
  | nop=nop_target; LBRACE; les=separated_list(COMMA, js_lexpr_target); RBRACE
    { 
      let les = match (nop : NOp.t) with 
        | SetInter
        | SetUnion -> JSExpr.SJSExpr.elements (JSExpr.SJSExpr.of_list les)
        | _ -> les in 
      NOp (nop, les) 
    }
(* - e *)
(* Unary negation has the same precedence as logical not, not as binary negation. *)
  | MINUS; e=js_lexpr_target
    { UnOp (UnaryMinus, e) } %prec unop_prec
(* {{ e, ..., e }} *)
  | LSTOPEN; exprlist = separated_nonempty_list(COMMA, js_lexpr_target); LSTCLOSE
    { EList exprlist }
(* -{- e, ..., e -}- *)
  | SETOPEN; exprlist = separated_list(COMMA, js_lexpr_target); SETCLOSE
    { ESet (JSExpr.SJSExpr.elements (JSExpr.SJSExpr.of_list exprlist)) }
(* l-nth(e1, e2) *)
  | LSTNTH; LBRACE; e1=js_lexpr_target; COMMA; e2=js_lexpr_target; RBRACE
    { BinOp (e1, LstNth, e2) }
(* s-nth(e1, e2) *)
  | STRNTH; LBRACE; e1=js_lexpr_target; COMMA; e2=js_lexpr_target; RBRACE
    { BinOp (e1, StrNth, e2) }
(* this *)
  | THIS { This }
(* (e) *)
  | LBRACE; e=js_lexpr_target; RBRACE
    { e }
(* _ *)
  | UNDERSCORE
    { LVar (JSLogicCommon.fresh_lvar ()) }
(* $$scope *)
  | SCOPELEXPR { Scope }
;

js_type_env_pair_target:
  | v = VAR; COLON; the_type=type_target
    { (v, the_type) }
  | v = LVAR; COLON; the_type=type_target
    { (v, the_type) }
;


js_macro_head_target:
 | name = VAR; LBRACE; params = separated_list(COMMA, js_lexpr_target); RBRACE
   { (name, params) }

js_var_and_le_target:
  | LBRACE; lvar = LVAR; DEFEQ; le = js_lexpr_target; RBRACE;
    { (lvar, le) }
;

(* [ def with #x := le1 and ... ] *)
js_unfold_info_target:
  | LBRACKET; id = VAR; WITH; var_les = separated_list(AND, js_var_and_le_target); RBRACKET
    { (id, var_les) }
;

js_logic_cmd_target:
(* fold x(e1, ..., en) *)
  | FOLD; assertion = js_assertion_target; fold_info = option(js_unfold_info_target)
    { 
      Printf.printf "Parsing a JS_FOLD with folding_info: %s\n" (JSLCmd.str_of_folding_info fold_info);
      Fold (assertion, fold_info) 
    }

(* unfold x(e1, ..., en) [ def1 with x1 := le1, ..., xn := len ] *)
  | UNFOLD; assertion = js_assertion_target; unfold_info = option(js_unfold_info_target)
    { Unfold (assertion, unfold_info) }

(* unfold_all x *)
  | UNFOLDALL; name = VAR;
    { GUnfold name }

(* flash x(e1, ..., en) *)
  | FLASH; assertion = js_assertion_target;
    { Flash (assertion) }

(* if(le) { lcmds } else { lcmds } *)
  | LIF; LBRACE; le=js_lexpr_target; RBRACE; LTHEN; CLBRACKET;
      then_lcmds = separated_list(SCOLON, js_logic_cmd_target);
      CRBRACKET; LELSE; CLBRACKET;
      else_lcmds = separated_list(SCOLON, js_logic_cmd_target);
       CRBRACKET;
    { If (le, then_lcmds, else_lcmds) }

(* if(e) { lcmd* } *)
  | LIF; LBRACE; le=js_lexpr_target; RBRACE; LTHEN; CLBRACKET;
      then_lcmds = separated_list(SCOLON, js_logic_cmd_target);
      CRBRACKET;
    { If (le, then_lcmds, []) }

  | macro = js_macro_head_target;
    { let (name, params) = macro in Macro (name, params) }

(* assert a *)
  | ASSERT; a = js_assertion_target; binders = option(binders_target);
    { Assert (a, Option.default [ ] binders) }

(* invariant a *)
  | INVARIANT; a = js_assertion_target
    { Invariant a  }

(* apply lemma_name(args) *)
   | APPLY; LEMMA; lemma_name = VAR; LBRACE; params = separated_list(COMMA, js_lexpr_target); RBRACE
     {
      ApplyLemma (lemma_name, params)
    }

(* use_subst [ spec_lab - #x: bla, #y: ble] *)
  | USESUBST; LBRACKET; spec_lab=VAR; MINUS; subst_lst = separated_nonempty_list(COMMA, js_lvar_le_pair_target); RBRACKET
     { 
        UseSubst(spec_lab, subst_lst)
     }

(* (lcmd) *)
  | LBRACE; lcmds=js_logic_cmd_target; RBRACE
    { lcmds }
;

js_logic_cmds_target:
  | lcmds = separated_list(SCOLON, js_logic_cmd_target); option(EOF);
    { lcmds }
;
