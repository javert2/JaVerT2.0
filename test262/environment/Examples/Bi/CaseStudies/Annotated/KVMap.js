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
  @id Map
*/
function Map () {
    /* Annotation */ isObject(this);
	this._contents = {};
	return this;
}

/*
  @id validKey
*/
function validKey (key) {
    /* Annotation */ isString(key);
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}

/*
  @id mapGet
*/
function mapGet (o, k) {
  /* Annotation */ isObject(o);
  /* Annotation */ isObject(o._contents);
  if (validKey(k)) {
	    if (o._contents.hasOwnProperty(k)) { 
	    	var result = o._contents[k];
	        return result
	    } else { return null }
	} else
	throw new Error("Invalid Key")
}

/*
  @id mapPut
*/
Map.prototype.put = function (o, k, v) {

  /* Annotation */ isObject(o);
  /* Annotation */ isObject(o._contents);
  if (validKey(k)) { 
    o._contents[k] = v; 
    return v;
  } else
    throw new Error("Invalid Key")
}