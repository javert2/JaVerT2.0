function Map () {
  this._contents = {};
  return this;
}

/* @id validKey */
Map.prototype.validKey = function (key) {
  return (typeof(key) === "string")
}

/* @id mapGet */
Map.prototype.get = function (k) {
  if (this.validKey(k)) { 
      if (this._contents.hasOwnProperty(k)) { 
        var result = this._contents[k];
          return result
      } else { return null }
  } else
  throw new Error("Invalid Key")
}

/* @id mapPut */
Map.prototype.put = function (k, v) {
  if (this.validKey(k)) { 
    this._contents[k] = v; 
    return v;
  } else
    throw new Error("Invalid Key")
}

var map = new Map();

var ivk = symb(ivk);
var tvk = typeof ivk;
Assume(not (tvk = "string"));

try {
  map.get(ivk);
} catch(e) {
  var msg = e.message;
  Assert(msg = "Invalid Key")
}

try {
  map.put(ivk);
} catch(e) {
  var msg = e.message;
  Assert(msg = "Invalid Key")
}