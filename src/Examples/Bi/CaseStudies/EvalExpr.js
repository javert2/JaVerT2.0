/* 
  @id evalUnop
*/
function evalUnop (op, l) { 

  switch (op) {
   case "-"   : return -l;
   case "not" : return !l;
   
   default : throw new Error ("Unsupported unary operator")
  }
}

/* 
  @id evalBinop
*/
function evalBinop (op, l1, l2) { 

  switch (op) { 
    case "+"   : return l1 + l2;
    case "-"   : return l1 - l2;
    case "or"  : return l1 || l2;
    case "and" : return l1 && l2;

    default : throw new Error("Unsupported binary operator")
  }
}

/*
  @id evalExpr
*/
function evalExpr (store, e) {

  if ((typeof e) !== "object") throw Error ("Unsupported expression");

  switch (e.category) {
    
    case "lit"   : return e.val;
    case "var"   : return store[e.name];
    case "binop" : return evalBinop (e.op, evalExpr(store, e.left), evalExpr(store, e.right)) 
    case "unop"  : return evalUnop  (e.op, evalExpr(store, e.arg)) 
    
    default : throw new Error("Unsupported expression")
  }
}