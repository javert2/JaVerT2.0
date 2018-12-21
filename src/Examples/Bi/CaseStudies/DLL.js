/** 
  Bug Specs:
    1. lst is undefined

  Success Specs:
    1. lst is empty 
    2. lst has one element

  @id listCopy 
*/
function listCopy (lst) {
  return (lst === null) ? null : { val: lst.val, prev: lst.prev, next : listCopy(lst.next) }
}

/** 
  Bug Specs:
    1. lb is undefined
    2. la is undefined

  Success Specs:
    1. la has one element, lb not empty
    2. la not empty, lb empty
    3. la empty, lb whatever
    4. la has more than one element, lb not empty (recursive case)

  @id listConcat
*/
function listConcat(la, lb) {
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