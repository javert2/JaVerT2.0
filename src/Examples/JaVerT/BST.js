/**
	@pred NullableObject(o) : 
		types (o : Obj),
		types (o : Null);

	@pred Node(+n : Obj, val : Num, left, right) :
		JSObject(n) *
		DataProp(n, "value", val) * DataProp(n, "left",  left) * DataProp(n, "right", right);

	@pred BST(+n, K : Set) :
		(n == null) * (K == -{ }-),
		
		Node(n, #val, #left, #right) * BST(#left, #KL) * BST(#right, #KR) * 
		(K == -u- (#KL, -{ #val }-, #KR)) * 
		(forall #x : Num. ((! (#x --e-- #KL)) \/ (#x <# #val))) *
		(forall #x : Num. ((! (#x --e-- #KR)) \/ (#val <# #x))) *
		types(#val : Num, #KL : Set, #KR : Set);
*/

/**
	@id makeNode
	
	@pre 
		(v == #v) * types (#v : Num)
		
	@post
		Node(#r, #v, null, null) * types (#r : Obj) * (ret == #r)
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

	@pre
		GlobalObject() * ObjectPrototype() * 
		(t == #t) * BST(#t, #K) * 
		(v == #v) * types (#v : Num) *
		scope(make_node : #makeNode) * JSFunctionObject(#makeNode, "makeNode", _, _, _) *
		scope(insert : #insert) * JSFunctionObject(#insert, "insert", _, _, _)
		
	@post 
		GlobalObject() * ObjectPrototype() * 
		BST(#t_new, -u- (#K, -{ #v }-)) * (ret == #t_new) * types (#t_new : Obj) *
		scope(make_node : #makeNode) * JSFunctionObject(#makeNode, "makeNode", _, _, _) *
		scope(insert : #insert) * JSFunctionObject(#insert, "insert", _, _, _)
*/
function insert(v, t)
{
  var result;
  
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
	
	@pre
		(t == #t) * BST(#t, #K) * (v == #v) * types (#v : Num) * 
		scope(find : #find) * JSFunctionObject(#find, "find", _, _, _) *
		GlobalObject() * ObjectPrototype() 

	@post 
		BST(#t, #K) * (ret == (#v -e- #K)) * 
		scope(find : #find) * JSFunctionObject(#find, "find", _, _, _) * 
		GlobalObject() * ObjectPrototype() 
*/
function find (v, t)
{
	var result;

	if (t === null)
		result = false;
	else if (v === t.value)
		result = true;
	else {
		if (v < t.value)
		  result = find(v, t.left) 
		else
		  result = find(v, t.right);
	}
	
	return result;
}

/**
	@id findMin
	
	@pre
		GlobalObject() * ObjectPrototype() *
		(t == #t) * BST(#t, #K) * types(#t : Obj) * 
		scope(find_min : #findMin) * JSFunctionObject(#findMin, "findMin", _, _, _)

	@post 
		GlobalObject() * ObjectPrototype() *
		BST(#t, #K) * (ret == #r) * types(#r : Num) * (#r --e-- #K) * 
		(forall #x : Num. ((! (#x --e-- #K)) \/ (#r <=# #x))) *
		scope(find_min : #findMin) * JSFunctionObject(#findMin, "findMin", _, _, _)
*/
function find_min(t)
{
	var result;
		
	if (t.left === null)
		result = t.value;
	else
		result = find_min(t.left);
		
	return result;
}

/**
	@id remove
		
	@pre
		GlobalObject() * ObjectPrototype() *
		(t == #t) * BST(#t, #K) * 
		(v == #v) * types (#v : Num) *
		scope(remove : #remove) * JSFunctionObject(#remove, "remove", _, _, _) *
		scope(find_min : #findMin) * JSFunctionObject(#findMin, "findMin", _, _, _)

	@post 
		GlobalObject() * ObjectPrototype() *
		(ret == #t_new) * BST(#t_new, #K_new) * (#K_new == #K -d- -{ #v }-) * NullableObject(#t_new) *
		scope(remove : #remove) * JSFunctionObject(#remove, "remove", _, _, _) *
		scope(find_min : #findMin) * JSFunctionObject(#findMin, "findMin", _, _, _)
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
			var min = find_min(t.right);
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