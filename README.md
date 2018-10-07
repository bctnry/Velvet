# Velvet
A stack-based concatenative programming language.

## How does it look like

There's the definition of factorial:
```
"fac"
    <=1 branch:[pop 1],[dup -1 fac *] ;
```
or:
```
"fac"
    "fac_iter:n,res"
        $n <=1 branch:[$res],[
          $n $res * ->res pop   // n * res -> res, leaving the stack with n on the top
          $n -1 ->n pop             // n - 1 -> n
          fac_iter:{$n},{$res}
        ]
    ;
    fac_iter:?,1
;
```
and there's an example of putting the sequence 1, 2, 3... onto the stack, with 1 at the top of the stack.
```
"iota"
    <=1 branch:[pop 1],[dup -1 iota] ;
```
a generalized version of `iota`:
```
"iota:start,step,end"
    $start >end branch:[],[iota:{$start $step +},{$step},{$end} start] ;
iota:1,2,10    // 1, 3, 5, 7, 9
```
