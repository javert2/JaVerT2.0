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

/**
    @id insert 
*/
function insert(node, value) {

    /* Annotation */ isNullableObject(node);
    /* Annotation */ isNumber(value);
    
    if (node === null) {
        return { next: null, value: value }
    } else {
      /* Annotation */ isNumber(node.value);
      if (node.value === value) {
        return node;
      } else if (node.value < value) {
        var rec = insert(node.next, value);
        return { next: rec, value: node.value }
      } else {
        return { next: node, value: value }
      }
    }
}

/** 
    @id sort 
*/
function sort(head) {

    /* Annotation */ isNullableObject(head);
    
    if (head === null) {
        return null
    } else {
        var rec = sort(head.next);
        return insert(rec, head.value)
    }
}

