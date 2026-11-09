# parsing-7: `parse_proof` says it reads like `fscanf(" %i ")`, and differs on `010` and `0x10`

**Proposed severity: Note.** A difference from drat-trim's reader that contradicts a sentence
in the docstring. Not run against drat-trim: it is not on PATH here. What I ran is the format
string itself, in C. No solver writes these spellings, so this affects hostile or hand-written
proofs only, and a different literal fails closed unless the clause happens to verify.

## Minimal case

`010 0\n`, and `0x10 0\n`.

## Reproducer

```python
from dratify import parse_proof, to_dimacs

print([[to_dimacs(l) for l in c] for _, c in parse_proof("010 0\n")])
try:
    parse_proof("0x10 0\n")
except ValueError as e:
    print(e)
```

```
[[10]]
proof line 1: bad token '0x10'
```

```c
#include <stdio.h>
int main(void){FILE*f=tmpfile();fputs("010 0x10 0\n",f);rewind(f);int x;
  while(fscanf(f," %i ",&x)==1)printf("%d\n",x);return 0;}
```

prints `8`, `16`, `0`. `src/dratify/proof.py:219-221` and CHANGELOG 0.1.10 describe the reader by
that format. The decimal reading here matches minisat, cadical and kissat on a CNF file: `010 0`
exits 10 on all three, though that test only shows they accept it, not which variable they read.

No oracle call applies: the oracle takes integers, and this is about which integer the text
is. The generator judges `010` as decimal, and says in `not_checked` that drat-trim was not run.

## Suspected cause

`int(num)` at `src/dratify/proof.py:251`. Both engines take this parse. The clearest fix is to the
docstring: say the two agree on decimal spellings without a leading zero. Reading `%i`'s octal
would be a poor choice. Refusing a leading zero in proofs is possible, if anyone wants it to
raise instead of differ.

## Proposed test

None until that is decided. If leading zeros are refused:

```python
import unittest

from dratify import parse_proof


class TestLeadingZeroInAProof(unittest.TestCase):
    def test_it_would_mean_octal_to_drat_trim(self):
        with self.assertRaises(ValueError):
            parse_proof("010 0\n")
```
