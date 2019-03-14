var x = fresh_symb("banana")
var tx = (typeof x === "number") && (x > 0); 
var y = fresh_symb("apple"); 
var ty = (typeof y === "number"); 
var t = tx && ty;
Assume (t);  
Assert ( (x + y) > 0)
