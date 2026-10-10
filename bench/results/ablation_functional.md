# The functional rows of the ablation table (generated Standard ML), scored like the chain

## smt: 326 cases, scoring cap 1 s, PAR2 in ms

| arm | row | PAR2 | completed | wrong | timeout | skipped | gm of completed (ms) |
|---|---|---|---|---|---|---|---|
| fn_dsc_exec | row 1, dsc_exec (rational, generated SML) | 79.6723 | 320 | 0 | 6 | 0 | 1.252 |
| fn_dsc_int | row 2, dsc_int (integer, generated SML) | 15.4866 | 326 | 0 | 0 | 0 | 0.4282 |
| fn_sturm | verified Sturm isolator (generated SML) | 194.1270 | 300 | 0 | 26 | 0 | 0.6791 |

| step | PAR2 ratio (new/old) | paired gm ratio (new/old) | cases both complete | completions | verdict |
|---|---|---|---|---|---|
| fn_dsc_exec -> fn_dsc_int (row 2, dsc_int (integer, generated SML)) | 0.194 | 0.303 | 320 | +6 | change |
| fn_dsc_int -> fn_sturm (verified Sturm isolator (generated SML)) | 12.535 | 2.291 | 300 | -26 | change |

## mpsolve: 131 cases, scoring cap 60 s, PAR2 in s

| arm | row | PAR2 | completed | wrong | timeout | skipped | gm of completed (ms) |
|---|---|---|---|---|---|---|---|
| fn_dsc_exec | row 1, dsc_exec (rational, generated SML) | 39.1378 | 92 | 0 | 39 | 0 | 250.9 |
| fn_dsc_int | row 2, dsc_int (integer, generated SML) | 22.2904 | 109 | 0 | 22 | 0 | 59.31 |
| fn_sturm | verified Sturm isolator (generated SML) | 51.4506 | 77 | 0 | 52 | 0 | 84.79 |

| step | PAR2 ratio (new/old) | paired gm ratio (new/old) | cases both complete | completions | verdict |
|---|---|---|---|---|---|
| fn_dsc_exec -> fn_dsc_int (row 2, dsc_int (integer, generated SML)) | 0.570 | 0.096 | 92 | +17 | change |
| fn_dsc_int -> fn_sturm (verified Sturm isolator (generated SML)) | 2.308 | 4.691 | 75 | -32 | change |

## and: 295 cases, scoring cap 150 s, PAR2 in s

| arm | row | PAR2 | completed | wrong | timeout | skipped | gm of completed (ms) |
|---|---|---|---|---|---|---|---|
| fn_dsc_exec | row 1, dsc_exec (rational, generated SML) | 289.0359 | 13 | 0 | 19 | 263 | 1.69e+04 |
| fn_dsc_int | row 2, dsc_int (integer, generated SML) | 236.4177 | 71 | 0 | 19 | 205 | 8342 |
| fn_sturm | verified Sturm isolator (generated SML) | 294.6323 | 7 | 0 | 19 | 269 | 6.588e+04 |

| step | PAR2 ratio (new/old) | paired gm ratio (new/old) | cases both complete | completions | verdict |
|---|---|---|---|---|---|
| fn_dsc_exec -> fn_dsc_int (row 2, dsc_int (integer, generated SML)) | 0.818 | 0.025 | 13 | +58 | change |
| fn_dsc_int -> fn_sturm (verified Sturm isolator (generated SML)) | 1.246 | 22.057 | 7 | -64 | change |

