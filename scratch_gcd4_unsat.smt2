; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x2021 (exists ((k Int) )(let (($x1518 (exists ((l Int) )(let ((?x1034 (* g l)))
 (= b ?x1034)))
 ))
 (and (= a (* g k)) $x1518)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x2021)) (>= 0 g))))
(assert
 (let (($x1628 (forall ((d Int) )(let ((?x1016 (+ g a)))
(let (($x224 (<= d ?x1016)))
(let (($x1585 (and (= a (* d (div a d))) (= b (* d (div b d))))))
(let (($x30 (>= 0 d)))
(or $x30 (or (> d a) (or (not $x1585) $x224))))))))
))
(let (($x265 (= b (* (+ g a) (div b (+ g a))))))
(let (($x735 (= a (* (+ g a) (div a (+ g a))))))
(not (and (< 0 (+ g a)) (and $x735 (and $x265 $x1628))))))))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x559 (exists ((k Int) )(let (($x792 (exists ((l Int) )(let ((?x77 (* g l)))
 (= b ?x77)))
 ))
 (and (= a (* g k)) $x792)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x559)) (>= 0 g))))
(assert
 (not false))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x1714 (exists ((k Int) )(let (($x1869 (exists ((l Int) )(let ((?x417 (* g l)))
 (= b ?x417)))
 ))
 (and (= a (* g k)) $x1869)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x1714)) (>= 0 g))))
(assert
 (let (($x919 (forall ((d Int) )(let ((?x778 (+ g a)))
(let (($x139 (<= d ?x778)))
(let (($x226 (and (= a (* d (div a d))) (= b (* d (div b d))))))
(let (($x737 (>= 0 d)))
(or $x737 (or (> d a) (or (not $x226) $x139))))))))
))
(let (($x1824 (= b (* (+ g a) (div b (+ g a))))))
(let (($x197 (= a (* (+ g a) (div a (+ g a))))))
(not (and (< 0 (+ g a)) (and $x197 (and $x1824 $x919))))))))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x437 (exists ((k Int) )(let (($x678 (exists ((l Int) )(let ((?x1523 (* g l)))
 (= b ?x1523)))
 ))
 (and (= a (* g k)) $x678)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x437)) (>= 0 g))))
(assert
 (not false))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x116 (exists ((k Int) )(let (($x1147 (exists ((l Int) )(let ((?x1839 (* g l)))
 (= b ?x1839)))
 ))
 (and (= a (* g k)) $x1147)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x116)) (>= 0 g))))
(assert
 (let (($x310 (forall ((d Int) )(let ((?x359 (+ g a)))
(let (($x942 (<= d ?x359)))
(let (($x2656 (and (= a (* d (div a d))) (= b (* d (div b d))))))
(let (($x694 (>= 0 d)))
(or $x694 (or (> d a) (or (not $x2656) $x942))))))))
))
(let (($x339 (= b (* (+ g a) (div b (+ g a))))))
(let (($x282 (= a (* (+ g a) (div a (+ g a))))))
(not (and (< 0 (+ g a)) (and $x282 (and $x339 $x310))))))))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x170 (exists ((k Int) )(let (($x2172 (exists ((l Int) )(let ((?x1403 (* g l)))
 (= b ?x1403)))
 ))
 (and (= a (* g k)) $x2172)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x170)) (>= 0 g))))
(assert
 (not false))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x2529 (exists ((k Int) )(let (($x2534 (exists ((l Int) )(let ((?x4507 (* g l)))
 (= b ?x4507)))
 ))
 (and (= a (* g k)) $x2534)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x2529)) (>= 0 g))))
(assert
 (let (($x449 (forall ((d Int) )(let ((?x722 (+ g a)))
(let (($x3272 (<= d ?x722)))
(let (($x2230 (and (= a (* d (div a d))) (= b (* d (div b d))))))
(let (($x6294 (>= 0 d)))
(or $x6294 (or (> d a) (or (not $x2230) $x3272))))))))
))
(let (($x100 (= b (* (+ g a) (div b (+ g a))))))
(let (($x90 (= a (* (+ g a) (div a (+ g a))))))
(not (and (< 0 (+ g a)) (and $x90 (and $x100 $x449))))))))
(check-sat)

; seed None timeout 1500
; benchmark generated from python API
(set-info :status unknown)
(declare-fun g () Int)
(declare-fun b () Int)
(declare-fun a () Int)
(assert
 (let (($x1528 (exists ((k Int) )(let (($x5675 (exists ((l Int) )(let ((?x1853 (* g l)))
 (= b ?x1853)))
 ))
 (and (= a (* g k)) $x5675)))
 ))
 (and (and (and (< 0 a) (< 0 b)) (and (< 0 g) $x1528)) (>= 0 g))))
(assert
 (not false))
(check-sat)

