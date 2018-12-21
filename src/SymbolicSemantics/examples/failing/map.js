/*get(m.put(k, v)) = v */


function Map () {
   this._contents = {};
}

function isValidKey (key) {
    return (typeof (key) === 'string') && (key !== '');
}


Map.prototype.get = function get (key) {
  var result;

  if (isValidKey(key)) { 
    if (this._contents.hasOwnProperty(key)) {
      result = this._contents[key] 
    } else {
      result = null 
    }  
    return result
  } else {
    throw new Error("Invalid Key")
  }
}


Map.prototype.put = function put (key, value) {
   if (isValidKey(key)) { 
       this._contents[key] = value; 
   } else {
       throw new Error("Invalid Key")
   } 
}

var s1 = symb_string (s1);
var n1 = symb_number (n1);
var m = new Map(); 

Assume(not (s1 = ""));

m.put(s1, n1); 
var key_val = m.get(s1); 

Assert(key_val = n1)
