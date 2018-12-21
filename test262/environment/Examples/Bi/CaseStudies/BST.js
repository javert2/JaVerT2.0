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

	@biabduction
    6 specs, 2 annots
*/
function find (v, t)
{
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
	
	@biabduction
    2 specs, 1 annots
*/
function findMin(t)
{
	if (t.left === null)
		return t.value;
	else
		return findMin(t.left);
}

/**
	@id remove
	
	@biabduction
    12 specs, 2 annots
*/
function remove(v, t)
{
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
