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
    @id make_node 
*/
function make_node(v)
{
  var node = {
    value : v,
    left  : null,
    right : null
  };
  return node;
}

/**
	@id insert
*/
function insert(v, t)
{
  /* Annotation */ isNumber(v); 
  /* Annotation */ isNullableObject(t);

  if (t === null) {
  	return make_node(v);
  }

  if (v < t.value)
    t.left = insert(v, t.left);
  else if (v > t.value) 
    t.right = insert(v, t.right);

  return t;
}

/**
	@id find
*/
function find (v, t)
{
    /* Annotation */ isNumber(v); 
    /* Annotation */ isNullableObject(t);

	if (t === null)
		return false;
	else if (v === t.value)
		return true;
	else {
		if (v < t.value)
		  return find(v, t.left) 
		else
		  return find(v, t.right);
	}
	
	return result;
}

/**
	@id findMin
*/
function findMin(t)
{
	/* Annotation */ isObject(t);

	if (t.left === null)
		return t.value;
	else
		return findMin(t.left);
}

/**
	@id remove
	
*/
function remove(v, t)
{
    /* Annotation */ isNumber(v); 
    /* Annotation */ isNullableObject(t);

	if (t === null)
		return null;

	if (v === t.value) {
		if (t.left === null) {	
				return t.right;
			}
		else 
		if (t.right === null) {
	  			return t.left;
			}
		else {
			var min = findMin(t.right);
			t.right = remove(min, t.right);
			t.value = min;
		}
	}
	else if (v < t.value)
		t.left = remove(v, t.left);
	else
		t.right = remove(v, t.right);	

  return t;
}
