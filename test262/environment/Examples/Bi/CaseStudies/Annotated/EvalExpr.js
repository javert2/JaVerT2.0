/* @id assumeType */
function assumeType(x, t) {
    var tx = typeof x;
    Assume(tx = t)
}

/* @id isBool */
function isBool(b) {
  assumeType(b, "boolean");
}

/* @id isNumber */
function isNumber(n) {
  assumeType(n, "number");
}

/* @id isString */
function isString(s) {
  assumeType(s, "string");
}

/* @id isObject */
function isObject(o) {
  assumeType(o, "object");
  Assume(not (o = null));
}

/* @id isNullableObject */
function isNullableObject(o) {
  assumeType(o, "object");
}

/* 
  @id evalUnop
*/
function evalUnop (op, l) { 

  isString(op);

  switch (op) {
   case "-"   : isNumber(l); return -l;
   case "not" : isBool(l); return !l;
   
   default : throw new Error ("Unsupported unary operator")
  }
}

/* 
  @id evalBinop
*/
function evalBinop (op, l1, l2) { 

  isString(op);

  switch (op) { 
    case "+"   : isNumber(l1); isNumber(l2); return l1 + l2;
    case "-"   : isNumber(l1); isNumber(l2); return l1 - l2;
    case "or"  : isBool(l1); isBool(l2); return l1 || l2;
    case "and" : isBool(l1); isBool(l2); return l1 && l2;

    default : throw new Error("Unsupported binary operator")
  }
}

/*
  @id evalExpr
*/
function evalExpr (store, e) {

  isNullableObject(e);

  if ((typeof e) !== "object") throw Error ("Illegal Expr!")

  switch (e.category) {
    
    case "binop" : return evalBinop (e.op, evalExpr(store, e.left), evalExpr(store, e.right)) 
    case "unop"  : return evalUnop  (e.op, evalExpr(store, e.arg)) 
    case "lit"   : return e.val
    case "var"   : isObject(store); return store[e.name];
    
    default : throw new Error("Illegal Expr!")
  }
}