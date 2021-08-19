import * as assert from 'assert'

/*
 * From Mozilla Developer Network:
 * The Promise.race(promises) method returns a promise that resolves or rejects
 * as soon as one of the promises in the array resolves or rejects,
 * with the value or reason from that promise.
 */
function race(promises) {
    return new Promise(function (resolve, reject) {
        for (let p  of promises){
            p.then(resolve);
            p.catch(reject);            
        }
    });
}


/*
 * Write a function that takes an arbitrarily
 * nested array and generates the sequence
 * of values from the array.
 * Example: [...flatten([1, [2, [3]], 4, [[5, 6], 7, [[[8]]]]])] => [1, 2, 3, 4, 5, 6, 7, 8]
 */
function* flatten(array) {
    for (let component of array)
    {
        if(!Array.isArray(component)) yield component;
        else{
            yield *flatten(component);
        }
    }
}
/*
 * Given two generators, write a function
 * that generates the interleaved sequence
 * of elements of both generators.
 * Example: given generators for even and odd
 * numbers, take(interleave(evens(), odds()), 8) => [0, 1, 2, 3, 4, 5, 6, 7]
 */
function *interleave(g1, g2) {
    let comp1 = g1.next();
    let comp2 = g2.next();
    while(!comp1.done || !comp2.done){
        if (!comp1.done){
            yield comp1.value;
            comp1 = g1.next();
        }
        if(!comp2.done){
            yield comp2.value;
            comp2 = g2.next();
        }
    }
}
/*
 * Write a function that continuously generates
 * elements of a given array in a cyclic manner.
 * Example: take(cycle([1, 2, 3]), 8) => [1, 2, 3, 1, 2, 3, 1, 2]
 */
function* cycle(array) {
    while (true)
    {
        for (let component of array)
        yield component;
    }
}

/*
 * Write a function that returns
 * all elements from the first array,
 * then all elements from the next array, etc.
 * This function lets us to treat an array of arrays
 * as a single collection.
 * Example: [...chain([['A', 'B'], ['C', 'D']])] => ['A', 'B', 'C', 'D']
 */
function* chain(arrays) {
    for (let array of arrays){
        for (let component of array)
        yield component;
    }
}

/*
 * In order to make testing your generators easier,
 * the function take takes a generator g and a natural number n
 * and returns an array of the first n elements of g.
 * If g is exhausted before reaching n elements,
 * less than n elements are returned. 
 */
function take(g, n) {
    const result = [];
    for (let i = 0; i < n; i++) {
        const {value,done} = g.next();
        if (done) {
            break;
        }
        result.push(value);
    }
    return result;
}

