---
sidebar_position: 6
---

# Builtin Functions

As of v0.10.0, Embr has a couple of builtin functions.

## clock()

Returns the length of time elapsed since the interpreter has started.

```embr
out clock();
```

## time()

Returns the current Unix timestamp.

```embr
out time();
```

## term(x)

Accepts a stringified terminal command, allowing Embr to run terminal commands on your computer.

```embr
term("code ."); // launches vscode if you have 'code' in your system path
term("echo hello embr!"); // echos 'hello embr!' in your terminal
```

## out

Outputs the evaluation of the remainder of the line into the console.

```embr
out "Hello, Embr!"; // Hello, Embr!
```

## length(x)

Takes one argument and returns the length. Can be an array or a string.

```embr
var my_arr = [1, 2, 3, 4, 5];
var hello = "Hello, Embr!";
out length(my_arr); // -> 5;
out length(hello); // -> 13;
```

## rest(x)
Rest accepts one argument, an array, removes the first element from the array, and returns a new array with the remaining elements.

```embr
var my_arr = [1, 2, 3, 4, 5];
out rest(my_arr); // -> returns [2, 3, 4, 5]
```

## tail(x)
Tail accepts one argument (an array), and returns the last element found in the array, and removes that element from the original array.

```embr
var my_arr = [1, 2, 3];
out tail(my_arr); // -> returns 3, my_arr is now [1, 2]
```

## head(x)
Head accepts one argument (an array), and returns the first element found in the array, and removes that element from the original array.

```embr
var my_arr = [1, 2, 3];
out head(my_arr); // -> returns 1, my_arr is now [2, 3]
```

## append(x, y)
Append accepts two arguments: an array, and a value.

```embr
var my_arr = [1, 2, 3];
out append(my_arr, 42); // -> [1, 2, 3, 42]
```

## prepend(x, y)

Prepend accepts two arguments: an array, and a value.

```embr
var my_arr = [1, 2, 3];
out prepend(my_arr, 42); // -> [42, 1, 2, 3]
```

## remove(x, y)

Remove accepts two arguments: a hash, and a key.

```embr
out my_hash; // -> {"hash table!": "first hash key!", dog: "Golden Retriever", apples: ["Golden Delicious", "Granny Smith"]}

remove(my_hash, "dog");

out my_hash; // -> {"hash table!": "first hash key!", apples: ["Golden Delicious", "Granny Smith"]}
```
