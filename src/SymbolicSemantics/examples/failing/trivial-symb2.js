var s  = symb_string(s); 
var n1 = symb_number(n1); 
var n2 = symb_number(n2); 

Assume(n1 > 0);

var o = {}; 
o["foo"] = n1; 
o["bar"] = n2; 

var z = o[s];
Assert(z > 0)