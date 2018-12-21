{
  open Lexing
  open CCommon
  
  let keyword_table = Hashtbl.create 307 
  
  let _ = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
  [ (* JS Logic tokens *)
    "scope",    JSIL_Parser.SCOPE;
      "schain",   JSIL_Parser.SCHAIN; 
      "this",     JSIL_Parser.THIS;
      "closure",  JSIL_Parser.CLOSURE;
      "sc_scope", JSIL_Parser.SCSCOPE;
      "o_chains", JSIL_Parser.OCHAINS;
      
      (* Type literals *)
      "Undefined", JSIL_Parser.UNDEFTYPELIT;
      "Null",      JSIL_Parser.NULLTYPELIT;
      "Empty",     JSIL_Parser.EMPTYTYPELIT;
      "None",      JSIL_Parser.NONETYPELIT;
      "Bool",      JSIL_Parser.BOOLTYPELIT;
      "Num",       JSIL_Parser.NUMTYPELIT;
      "Str",       JSIL_Parser.STRTYPELIT;
      "Obj",       JSIL_Parser.OBJTYPELIT;
      "List",      JSIL_Parser.LISTTYPELIT;
      "Type",      JSIL_Parser.TYPETYPELIT;
      "Set",       JSIL_Parser.SETTYPELIT;
      
      (* Literals *)
      "undefined", JSIL_Parser.UNDEFINED;
      "null",      JSIL_Parser.NULL;
      "empty",     JSIL_Parser.EMPTY;
      "true",      JSIL_Parser.TRUE;
      "false",     JSIL_Parser.FALSE;
      "nan",       JSIL_Parser.NAN;
      "inf",       JSIL_Parser.INFINITY;
      "nil",       JSIL_Parser.LSTNIL;
      
      (* Binary operators *)
      "and",     JSIL_Parser.AND;
      "or",      JSIL_Parser.OR;
      "m_atan2", JSIL_Parser.M_ATAN2;
      
      (* Unary operators *)
      "not",           JSIL_Parser.NOT;
      "isNaN",         JSIL_Parser.M_ISNAN;
      "m_abs",         JSIL_Parser.M_ABS;
      "m_acos",        JSIL_Parser.M_ACOS;
      "m_asin",        JSIL_Parser.M_ASIN;
      "m_atan",        JSIL_Parser.M_ATAN;
      "m_ceil",        JSIL_Parser.M_CEIL;
      "m_cos",         JSIL_Parser.M_COS;
      "m_exp",         JSIL_Parser.M_EXP;
      "m_floor",       JSIL_Parser.M_FLOOR;
      "m_log",         JSIL_Parser.M_LOG;
      "m_round",       JSIL_Parser.M_ROUND;
      "m_sgn",         JSIL_Parser.M_SGN;
      "m_sin",         JSIL_Parser.M_SIN;
      "m_sqrt",        JSIL_Parser.M_SQRT;
      "m_tan",         JSIL_Parser.M_TAN;
      "num_to_string", JSIL_Parser.TOSTRING;
      "num_to_int",    JSIL_Parser.TOINT;
      "num_to_uint16", JSIL_Parser.TOUINT16;
      "num_to_int32",  JSIL_Parser.TOINT32;
      "num_to_uint32", JSIL_Parser.TOUINT32;
      "string_to_num", JSIL_Parser.TONUMBER;
      "car",           JSIL_Parser.CAR;
      "cdr",           JSIL_Parser.CDR;
      "set_to_list",   JSIL_Parser.SETTOLIST;
      
      (* Expression keywords *)
      "typeOf", JSIL_Parser.TYPEOF;
      
      
      (* Command keywords *)
      "skip",         JSIL_Parser.SKIP;
      "new",          JSIL_Parser.NEW;
      "delete",       JSIL_Parser.DELETE;
      "deleteObject", JSIL_Parser.DELETEOBJ;
      "hasField",     JSIL_Parser.HASFIELD;
      "getFields",    JSIL_Parser.GETFIELDS;
      "metadata",     JSIL_Parser.METADATA; 
      "args",         JSIL_Parser.ARGUMENTS;
      "goto",         JSIL_Parser.GOTO;
      "with",         JSIL_Parser.WITH;
      "apply",        JSIL_Parser.APPLY;
      "PHI",          JSIL_Parser.PHI;
      "return",       JSIL_Parser.RETURN;
      "throw",        JSIL_Parser.THROW;
      "extern",       JSIL_Parser.EXTERN;
      
      (* Logical expressions: most match with the program expressions *)
      "none", JSIL_Parser.LNONE;
      
      (* Logic assertions *)
      "True",         JSIL_Parser.LTRUE;
      "False",        JSIL_Parser.LFALSE;
      "emp",          JSIL_Parser.LEMP;
      "types",        JSIL_Parser.LTYPES;
      "forall",       JSIL_Parser.LFORALL;
      "empty_fields", JSIL_Parser.EMPTYFIELDS;
      "MetaData",     JSIL_Parser.LMETADATA;
      "Extensible",   JSIL_Parser.LEXTENSIBLE;
      
      (* Logic predicates *)
      "pure", JSIL_Parser.PURE;
      "pred", JSIL_Parser.PRED;
      
      (* Logic commands *)
      "fold",         JSIL_Parser.FOLD;
      "flash",        JSIL_Parser.FLASH;
      "unfold",       JSIL_Parser.UNFOLD;
      "unfold_all",   JSIL_Parser.UNFOLDALL;
      "callspec",     JSIL_Parser.CALLSPEC;
      "if",           JSIL_Parser.LIF;
      "then",         JSIL_Parser.LTHEN;
      "else",         JSIL_Parser.LELSE;
      "macro",        JSIL_Parser.MACRO;
      "invariant",    JSIL_Parser.INVARIANT;
      "assert",       JSIL_Parser.ASSERT;
      "assume",       JSIL_Parser.ASSUME;
      "assume_type",  JSIL_Parser.ASSUME_TYPE;
      "spec_var",     JSIL_Parser.SPEC_VAR;
      "bind",         JSIL_Parser.BIND;
      "existentials", JSIL_Parser.EXISTENTIALS;
      "sep_assert",   JSIL_Parser.SEPASSERT;
      "sep_apply",    JSIL_Parser.SEPAPPLY;
      "branch",       JSIL_Parser.BRANCH;
      "use_subst",    JSIL_Parser.USESUBST;
      
     (* JS only spec specifics *)
     "js_only_spec", JSIL_Parser.JSOS;
      
      (* Procedure specification keywords *)
      "only",    JSIL_Parser.ONLY;
      "lemma",   JSIL_Parser.LEMMA;
      "variant", JSIL_Parser.VARIANT;
      "spec",    JSIL_Parser.SPEC;
      "bispec",  JSIL_Parser.BISPEC;
      "normal",  JSIL_Parser.NORMAL;
      "error",   JSIL_Parser.ERROR;
      
      (* JS only spec specifics *)
      "js_only_spec", JSIL_Parser.JSOS;
      "pre:",         JSIL_Parser.JSOSPRE;
      "post:",        JSIL_Parser.JSOSPOST;
      "outcome:",     JSIL_Parser.JSOSOUT;
      
      (* Procedure definition keywords *)
      "proc", JSIL_Parser.PROC;

    (* Others *)
    "import", JSIL_Parser.IMPORT
    ]
}

let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let identifier = letter(letter|digit|'_')*

let float = '-'? digit+ ('.' digit*)?

let var2 = "_pvar_" (letter|digit|'_')*
let filename = (letter|digit|'_')+ '.' (letter|digit|'_')+
let lvar = '#' (letter|digit|'_'|'$')*
let lvar2 = "_lvar_" (letter|digit|'_')*
let normalised_lvar = "##NORMALISED_LVAR" (letter|digit|'_'|'$')*
let loc = "$l" (letter|digit|'_')*
let aloc = "_$l_" (letter|digit|'_')*
let normalised_aloc = "_$l_#" (letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | white                { read lexbuf }
  | newline              { new_line lexbuf; read lexbuf }
  
  (* JS Logic tokens *)
  | "$$scope"            { JSIL_Parser.SCOPELEXPR    }
  | "_"                  { JSIL_Parser.UNDERSCORE    }
  
  (* Literals *)
  | "{{"        { JSIL_Parser.LSTOPEN   }
  | "}}"        { JSIL_Parser.LSTCLOSE  }
  
(* Constants *)
  | "$$min_float"        { JSIL_Parser.MIN_FLOAT     }
  | "$$max_float"        { JSIL_Parser.MAX_FLOAT     }
  | "$$random"           { JSIL_Parser.RANDOM        }
  | "$$e"                { JSIL_Parser.E             }
  | "$$ln10"             { JSIL_Parser.LN10          }
  | "$$ln2"              { JSIL_Parser.LN2           }
  | "$$log2e"            { JSIL_Parser.LOG2E         }
  | "$$log10e"           { JSIL_Parser.LOG10E        }
  | "$$pi"               { JSIL_Parser.PI            }
  | "$$sqrt1_2"          { JSIL_Parser.SQRT1_2       }
  | "$$sqrt2"            { JSIL_Parser.SQRT2         }
  | "$$UTCTime"          { JSIL_Parser.UTCTIME       }
  | "$$LocalTime"        { JSIL_Parser.LOCALTIME     }
    
(* Binary operators *)
  | "="                  { JSIL_Parser.EQUAL         }
  | "<"                  { JSIL_Parser.LESSTHAN      }
  | ">"                  { JSIL_Parser.GREATERTHAN   }
  | "<="                 { JSIL_Parser.LESSTHANEQUAL }
  | ">="                 { JSIL_Parser.GREATERTHANEQUAL }
  | "<s"                 { JSIL_Parser.LESSTHANSTRING}
  | "+"                  { JSIL_Parser.PLUS          }
  | "-"                  { JSIL_Parser.MINUS         }
  | "*"                  { JSIL_Parser.TIMES         }
  | "/"                  { JSIL_Parser.DIV           }
  | "%"                  { JSIL_Parser.MOD           }
  | "&"                  { JSIL_Parser.BITWISEAND    }
  | "|"                  { JSIL_Parser.BITWISEOR     }
  | "^"                  { JSIL_Parser.BITWISEXOR    }
  | "<<"                 { JSIL_Parser.LEFTSHIFT     }
  | ">>"                 { JSIL_Parser.SIGNEDRIGHTSHIFT }
  | ">>>"                { JSIL_Parser.UNSIGNEDRIGHTSHIFT }
  | "**"                 { JSIL_Parser.M_POW         }
  | "::"                 { JSIL_Parser.LSTCONS       }
  | "l+"                 { JSIL_Parser.LSTCAT        }
  | "++"                 { JSIL_Parser.STRCAT        }
  | "-u-"                { JSIL_Parser.SETUNION      }
  | "-i-"                { JSIL_Parser.SETINTER      }
  | "-d-"                { JSIL_Parser.SETDIFF       }
  | "-e-"                { JSIL_Parser.SETMEM        }
  | "-s-"                { JSIL_Parser.SETSUB        }
  | "--e--"              { JSIL_Parser.LSETMEM       }
  | "--s--"              { JSIL_Parser.LSETSUB       }
  | "-{"                 { JSIL_Parser.SETOPEN       }
  | "}-"                 { JSIL_Parser.SETCLOSE      }
(* Unary operators *)
  (* Unary minus uses the same symbol as binary minus, token MINUS *)
  | "~"                  { JSIL_Parser.BITWISENOT    }
  | "l-len"              { JSIL_Parser.LSTLEN }
  | "l-rev"              { JSIL_Parser.LSTREV }
  | "s-len"              { JSIL_Parser.STRLEN }
(* Expression keywords *)
  | "make-symbol-number" { JSIL_Parser.RNUMSYM }
  | "make-symbol-string" { JSIL_Parser.RSTRSYM }
  | "make-symbol-bool"   { JSIL_Parser.RBLNSYM }
  | "l-nth"              { JSIL_Parser.LSTNTH }
  | "s-nth"              { JSIL_Parser.STRNTH }
(* Command keywords *)
  | ":="                 { JSIL_Parser.DEFEQ }
(* Logic assertions *)
  | "[["                 { JSIL_Parser.OASSERT }
  | "]]"                 { JSIL_Parser.CASSERT }
  | "/\\"                { JSIL_Parser.LAND }
  | "\\/"                { JSIL_Parser.LOR }
  | "!"                  { JSIL_Parser.LNOT }
  | "=="                 { JSIL_Parser.LEQUAL }
  | "<#"                 { JSIL_Parser.LLESSTHAN       }
  | "<=#"                { JSIL_Parser.LLESSTHANEQUAL  }
  | "<s#"                { JSIL_Parser.LLESSTHANSTRING }
  (* Separating conjunction uses the same symbol as product, token TIMES *)
  | "->"                 { JSIL_Parser.LARROW      }
(* Logic commands *)
  | "[*"                 { JSIL_Parser.OLCMD     }
  | "*]"                 { JSIL_Parser.CLCMD     }
  | "[+"                 { JSIL_Parser.OOLCMD    }
  | "+]"                 { JSIL_Parser.CCLCMD    }
  | "unfold*"            { JSIL_Parser.RECUNFOLD }
  (**
    macro, assert are elsewhere
  *)
(* JS only spec specifics *)
  | "pre:"               { JSIL_Parser.JSOSPRE   }
  | "post:"              { JSIL_Parser.JSOSPOST  }
  | "outcome:"           { JSIL_Parser.JSOSOUT   }
(* Separators *)
  | "(*"                 { read_comment lexbuf   }
  | '.'                  { JSIL_Parser.DOT       }
  | ','                  { JSIL_Parser.COMMA     }
  | ':'                  { JSIL_Parser.COLON     }
  | ';'                  { JSIL_Parser.SCOLON    }
  | '('                  { JSIL_Parser.LBRACE    }
  | ')'                  { JSIL_Parser.RBRACE    }
  | '['                  { JSIL_Parser.LBRACKET  }
  | ']'                  { JSIL_Parser.RBRACKET  }
  | '{'                  { JSIL_Parser.CLBRACKET }
  | '}'                  { JSIL_Parser.CRBRACKET }
(* Literals (cont.) *)
  | float                { let n = float_of_string (Lexing.lexeme lexbuf) in
                             JSIL_Parser.FLOAT n }
  | '"'                  { read_string (Buffer.create 17) lexbuf }
  | loc                  { JSIL_Parser.LOC (Lexing.lexeme lexbuf) }
  | aloc                  { JSIL_Parser.ALOC (Lexing.lexeme lexbuf) }
  | normalised_aloc       { JSIL_Parser.ALOC (Lexing.lexeme lexbuf) }
(* Filenames *)
  | filename             { JSIL_Parser.FILENAME (Lexing.lexeme lexbuf) }
  
  (* Variables: THIS IS NEW *)
  | identifier           { let candidate = Lexing.lexeme lexbuf in 
                            (match (Hashtbl.mem keyword_table candidate) with
                            | true  -> Hashtbl.find keyword_table candidate
                            | false -> JSIL_Parser.VAR (Lexing.lexeme lexbuf)) }
                            
  | var2                 { JSIL_Parser.VAR (Lexing.lexeme lexbuf) }
(* Logic variables *)
  | lvar                 { JSIL_Parser.LVAR (Lexing.lexeme lexbuf) }
  | lvar2                { JSIL_Parser.LVAR (Lexing.lexeme lexbuf) }
  | normalised_lvar      { JSIL_Parser.LVAR (Lexing.lexeme lexbuf) }
(* EOF *)
  | eof                  { JSIL_Parser.EOF }
  | _                    { raise (Syntax_error ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
and
(* Read strings *)
read_string buf =
  parse
  | '"'                  { JSIL_Parser.STRING (Buffer.contents buf) }
  | '\\' '/'             { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\'            { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'             { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'             { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'             { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'             { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'             { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | '\\' '\"'            { Buffer.add_char buf '\"'; read_string buf lexbuf }
  | [^ '"' '\\']+        {
                           Buffer.add_string buf (Lexing.lexeme lexbuf);
                           read_string buf lexbuf
                         }
  | _                    { raise (Syntax_error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof                  { raise (Syntax_error ("String is not terminated")) }
and
(* Read comments *)
read_comment =
  parse
  | "*)"                 { read lexbuf }
  | eof                  { raise (Syntax_error ("Comment is not terminated")) }
  | _                    { read_comment lexbuf }
