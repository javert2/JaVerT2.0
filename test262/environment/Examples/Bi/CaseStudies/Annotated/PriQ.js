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
	@id Node
*/
function Node (pri, val) {
    /* Annotation */ isObject(this);
	this.pri = pri; 
	this.val = val; 
	this.next = null;
}

/*
	@id nodeInsert
*/
function nodeInsert (n, nl) {

    /* Annotation */ isObject(n);
    /* Annotation */ isNullableObject(nl);

	if (nl === null) {
	   return n
	}
    
    /* Annnotation */ isNumber(n.pri);
    /* Annnotation */ isNumber(nl.pri);
    
	if (n.pri > nl.pri) {
	   n.next = nl;
	   return n
	}
	
	var tmp = nodeInsert(n, nl.next);
	nl.next = tmp;
	return nl
}

/*
	@id PQ
*/
function PQ () {
    /* Annotation */ isObject(this);
	this._head = null;
};

/*
	@id pqEnqueue
*/
function pqEnqueue (q, pri, val) {
    /* Annotation */ isObject(q);
	var n = { pri: pri, val: val, next: null };
	q._head = nodeInsert(n, q._head);
};

/*
	@id pqDequeue
*/
function pqDequeue (q) {
  /* Annotation */ isObject(q);
  /* Annotation */ isNullableObject(q._head);
  if (q._head === null) {
    throw new Error("Queue is empty");
  }

  var first = q._head;
  q._head = q._head.next;
  return {pri: first.pri, val: first.val};
};
