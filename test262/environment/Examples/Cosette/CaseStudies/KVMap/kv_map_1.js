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

var k1 = symb_string(k1);
var k2 = symb_string(k2);

var v1 = symb(v1);

var map = new Map();
var cts = map._contents;
var props = Object.keys(cts);
var lprps = props.length;
Assert(lprps = 0);

map.put(k1, v1);
var props = Object.keys(cts);
var lprps = props.length;
var elmnt = props[0];
Assert((lprps = 1) and (elmnt = k1));

var v = map.get(k2);
Assert(((k1 = k2) and (v = v1)) or (v = null))