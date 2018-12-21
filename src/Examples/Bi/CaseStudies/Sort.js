/*
  Bug Specs:
    1. node is undefined

  @id insert 
*/
function insert(node, value) {
    
    if (node === null) {
        return { next: null, value: value }
    } else {
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
  Bug Specs:
    1. head is undefined

  @id sort 
*/
function sort(head) {    
    if (head === null) {
        return null
    } else {
        var rec = sort(head.next);
        return insert(rec, head.value)
    }
}

