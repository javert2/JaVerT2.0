/*
  @id Map
*/
function Map () {
	this._contents = {};
	return this;
}

/*
  @id validKey
*/
function validKey (key) {
	return (typeof(key) === "string" && key !== "hasOwnProperty")
}

/*
  @id mapGet
*/
function mapGet (o, k) {
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

  if (validKey(k)) { 
    o._contents[k] = v; 
    return v;
  } else
    throw new Error("Invalid Key")
}