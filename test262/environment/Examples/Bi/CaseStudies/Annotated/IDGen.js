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
  Success specs:
    1. Creation of ID Generator

  @id makeIdGen 
*/
var makeIdGen = function (prefix) { 

	var count = 0; 

    /* 
      Success specs:
        1. prefix is a string

	  @id getId 
	*/
	var getId = function () { 
        /* Annotation */ isString(prefix);
		return prefix + "_id_" + (count++) 
	}; 

	/* 
      Success specs:
        1. count is set to 0

	  @id reset 
	*/
	var reset = function () { 
		count = 0 
	}; 

	return { 
		getId: getId, 
		reset: reset 
	}
};