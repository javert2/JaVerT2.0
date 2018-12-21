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
  Annotations: 
    1. lst is a nullable object

  Success Specs:
    1. lst is empty 
    2. lst has one element

  @id listCopy 
*/
function listCopy (lst) {
  /* Annotation */ isNullableObject(lst);
  return (lst === null) ? null : { val: lst.val, prev: lst.prev, next : listCopy(lst.next) }
}

/** 
  Annotations:
    1. la is a nullable object
    2. lb is a nullable object

  Success Specs:
    1. la has one element, lb not empty
    2. la empty, lb not empty
    3. la not empty, lb empty
    4. la empty, lb empty
    5. la has more than one element, lb not empty (recursive case)

  @id listConcat
*/
function listConcat(la, lb) {
  /* Annotation */ isNullableObject(la);
  /* Annotation */ isNullableObject(lb);
  if (la === null) return lb;
  if (lb === null) return la;

  if (la.next === null) { la.next = lb; lb.prev = la; return la }

  la.next = listConcat(la.next, lb);
  return la
}

/** 
  Success Specs:
    1. lst has one element
    2. lst has more than one element
    3. lst is empty

  @id listAppend 
*/
function listAppend(lst, v) {
  var newNode = { val: v, prev : null, next : null };
  return (lst === null) ? newNode : listConcat(lst, newNode) 
}