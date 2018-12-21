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
  Success Specs:
    1. lst is empty 
    2. lst has one element

  @id listCopy  
*/
function listCopy (lst) { 
  /* Annotation */ isNullableObject(lst);
  return (lst === null) ? null : { val: lst.val, next : listCopy(lst.next) }
}

/** 
  Success Specs:
    1. la empty, lb whatever 
    2. la not empty, lb whatever (recursive case)

  @id listConcat
*/
function listConcat(la, lb) {

  /* Annotation */ isNullableObject(la);

  if (la === null) return lb; 

  la.next = listConcat(la.next, lb);
  return la
}

/** 
  Success Specs:
    1. lst has one element
    2. lst is empty

  @id listAppend 
*/
function listAppend(lst, v) {
  var newNode = { val: v, next : null };
  return (lst === null) ? newNode : listConcat(lst, newNode) 
}