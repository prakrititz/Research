# he_160_do_algebra

`doAlgebra(operator : List String, operand : List Int) : Int`

Given a list of operators (+, -, *, // floor division, ** exponentiation) and a list of non-negative integers with one more element than the operator list, build the algebraic expression operand[0] operator[0] operand[1] ... and return its evaluation with the usual precedence (** binds tightest and associates to the right, then * and //, then + and -, which associate to the left).
