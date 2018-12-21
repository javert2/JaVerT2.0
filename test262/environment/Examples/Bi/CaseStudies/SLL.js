/** 
  Bug Specs:
    1. lst is undefined

  Success Specs:
    1. lst is empty 
    2. lst has one element

  @id listCopy  
*/
function listCopy (lst) { 
  return (lst === null) ? null : { val: lst.val, next : listCopy(lst.next) }
}

/** 
  Bug Specs:
    1. la is undefined

  Success Specs:
    1. la empty, lb whatever 
    2. la not empty, lb whatever (recursive case)

  @id listConcat
*/
function listConcat(la, lb) {

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