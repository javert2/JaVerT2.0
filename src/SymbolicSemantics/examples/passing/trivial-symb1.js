var s = symb_string(s)
var n = symb_number(n)

var o = {}; 
o["foo"] = n; 

Assume(n > 0);
Assume(s = "foo");

var z = o[s];
Assert(z < 0)