// ------------------------------ base.js ----------------------------------


/* @id defaultEquals */
function defaultEquals (a, b) {
    return a === b;
};

/* @id isUndefined */
function isUndefined (obj) {
    return obj === undefined;
}

/* @id isString */
function isString (s) {
    return (typeof s === "string")
}

/* 
    @id defaultToString 
    @biabduce true
*/
function defaultToString (item) {
    if (item === null) {
        return 'BUCKETS_NULL';
    }
    if (isUndefined(item)) {
        return 'BUCKETS_UNDEFINED';
    }
    if (isString(item)) {
        return item;
    }
    Assume(false);
    return item.toString();
}

// ------------------------------ arrays.js ----------------------------------

/** @id indexOf */
function indexOf (array, item) {
    var length = array.length, i;
    Assume((length = 0) or (length = 1) or (length = 2)); 
    for (i = 0; i < length; i += 1) {
        if (defaultEquals(array[i], item)) {
            return i;
        }
    }
    Assume(false);
    return -1;
}


/** @id aRemove */
function aRemove (array, item) {
    var index = indexOf(array, item);
    if (index < 0) {
        return false;
    }
    array.splice(index, 1);
    return true;
}


/** @id dictionary */
function Dictionary () {

    var dictionary = {},
        table = {},
        nElements = 0; 

    /** @id dGet */
    dictionary.dGet = function(key) {
        var t_table = typeof table; 
        Assume((t_table = "object") and (not (table = null))); 
        var pair = table['/$ ' + defaultToString(key)];
        if (isUndefined(pair)) {
            return undefined;
        }
        return pair.value;
    };

    /** @id dRemove */
    dictionary.dRemove = function (key) {
        var k = '/$ ' + defaultToString(key),
            previousElement = table[k];
        if (isUndefined(previousElement)) {
            delete table[k];
            nElements -= 1;
            return previousElement.value;
        }
        return undefined;
    };

    return dictionary;
};


// --------------------------- multidictionary.js ----------------------------

/* @id multidictionary */

function MultiDictionary () {

    var multiDict = {},
        parent = new Dictionary();

     /** @id mRemove */
    multiDict.mRemove = function (key, value) {     
        Assume ((not (value = undefined)) and (not (key = undefined)) and (not (key = null))); 
        var v, array;
        if (isUndefined(value)) {
            v = parent.dRemove(key);
            if (isUndefined(v)) {
                return false;
            }
            return true;
        }
        array = parent.dGet(key);
        if (aRemove(array, value)) {
            if (array.length === 0) {
                Assume (false);
                parent.dRemove(key);
            }
            return true;
        }
        return false;
    };

    return multiDict;
};