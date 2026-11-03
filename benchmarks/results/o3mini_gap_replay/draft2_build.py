import sys
sys.path.insert(0, sys.argv[1])
from FormalLLM.lean.lemmas import LEMMAS
draft = open(sys.argv[2], encoding="utf-8").read()
ex = open(sys.argv[3], encoding="utf-8").read()
i = LEMMAS.rindex("end Refine")
open(sys.argv[4], "w", encoding="utf-8").write("import Mathlib\n" + LEMMAS[:i] + draft + "\n" + LEMMAS[i:] + ex)
