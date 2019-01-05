;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; skeleton-decode - deserialisation routines for Register Key data
;;;
;;; gov.uk Open Registers are a way of expressing an authoritative list that
;;; you can trust.
;;;
;;; skeleton is a key encoding that can represent a range of primitive and
;;; user defined types. The encoded data is always valid UTF-8 that sorts in
;;; the same order as you would expect the unencoded data to sort in its native
;;; type. i.e. numbers sort in numerical order rather than in string prefix
;;; order. The numbers model allows for exact representation of rational
;;; numbers of unlimited size and precision.
;;;
;;; skeleton provides serialisers and deserialisers that can deal with the low
;;; level encoding scheme that ensures Register Key data always sorts in the
;;; correct order for its type across all Regiser implementations,
;;; independently of platform, language or backing store. Moreover, the encoded
;;; keys always consist only of printable characters which makes them suitable
;;; for embedding in other formats and protocols.
;;;
;;;
;;;  Copyright (C) 2019, Andy Bennett, Register Dynamics Limited.
;;;  All rights reserved.
;;;
;;;  Redistribution and use in source and binary forms, with or without
;;;  modification, are permitted provided that the following conditions are met:
;;;
;;;  Redistributions of source code must retain the above copyright notice, this
;;;  list of conditions and the following disclaimer.
;;;  Redistributions in binary form must reproduce the above copyright notice,
;;;  this list of conditions and the following disclaimer in the documentation
;;;  and/or other materials provided with the distribution.
;;;  Neither the name of the author nor the names of its contributors may be
;;;  used to endorse or promote products derived from this software without
;;;  specific prior written permission.
;;;
;;;  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;;  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;;  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;;  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE
;;;  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;;  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;;  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;;  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;;  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;;  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;;  POSSIBILITY OF SUCH DAMAGE.
;;;
;;; Andy Bennett <andyjpb@register-dynamics.co.uk>, 2019/01/04
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import chicken scheme)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use numbers comparse base64)


;;;;;;;;;;
;;; Helpers

(define (skeleton-decode-decode-abort . x)
  (fprintf (current-error-port) "\nSkeleton (Decode) Aborting!\n\n")
  (apply abort x))

; Returns a procedure useful as the proc argument to bind that checks whether a
; single character is in the specified range.
(define (char-in-range min max)
  (lambda (c)
    (let ((c* (char->integer c)))
      (if (and (>= c* min) (<= c* max))
	(result c)
	fail))))

; Takes a list of procedures that return `(result c)` or `fail` and returns
; `(result c)` if any of the procedures return `(result c)` and returns `fail`
; otherwise.
; This is used to compose multiple char-in-range checks.
(define (check-any . procs)
  (lambda (c)
    (fold ; TODO: stop on first #t value
      (lambda (p s)
	(if (eqv? s fail)
	  (p c)
	  s))
      fail
      procs)))

(define (decode-regular-magnitude value seed)
  (+ (* seed 32)
     (bitwise-and #x1f (char->integer value))))

(define (decode-complement-magnitude value seed)
  (+ (* seed 32)
     (- 32
	(bitwise-and #x1f (char->integer value)))))

; We get a list of list of chars thus:
;   ((#\0 #\4) (#\0 #\5)))
; Each inner list always contains two chars.
(define (decode-regular-integer chars)
  (fold
    (lambda (c s)
      (+
	(* s 16)
	; We know c is in [0-9A-Z].
	(let ((c (char->integer c)))
	  (if (> c #x39)    ; c > '9' => in [A-Z]
	    (- c #x37)      ; Return c - 'A' - 10
	    (- c #x30)))))  ; Return c - '0'
    0
    (flatten chars)))

; We get a list of list of chars thus:
;   ((#\0 #\4) (#\0 #\5)))
; Each inner list always contains two chars.
(define (decode-complement-integer chars)
  (+ 1
     (fold
       (lambda (c s)
	 (+
	   (* s 16)
	   ; We know c is in [0-9A-Z].
	   (let ((c (char->integer c)))
	     (if (> c #x39)    ; c > '9' => in [A-Z]
	       (- #x46 c)      ; Return 'F' - c
	       (- #x3F c)))))  ; Return '9' + 6 - c
       0
       (flatten chars))))

; Converge a Continued Fraction.
; i.e. Grind it into the internal number representation.
(define (converge whole fractions)

 ; h_n = a_n * h_(n-1) + h_(n-2)
 (define (converge* t** t* n terms) ; h_(n-2) h_(n-1) a_n
   (if (null? terms)
     (+ (* n t*) t**)
     (converge*
       t*
       (+ (* n t*) t**)
       (car terms)
       (cdr terms))))

 (/
  (converge* 0 1 whole fractions)   ; numerator   h_n = a_n * h_(n-1) + h_(n-2)
  (converge* 1 0 whole fractions))) ; denominator k_n = a_n * k_(n-1) + k_(n-2)



;;;;;;;;;;
;;; Rules of the Grammar
;;; orc/doc/skeleton.txt

(define void*
  (sequence* ((v (char-seq "!")))
    (result (void))))

(define false
  (sequence* ((f (char-seq "$")))
    (result #f)))

(define true
  (sequence* ((t (char-seq "%")))
    (result #t)))

(define boolean
  (any-of
    false
    true))

(define primitive-typecode
  (any-of
    (char-seq "!")     ; void
    (char-seq "#")     ; boolean
    (char-seq "/")     ; typecode
    (char-seq "=")     ; number
    (char-seq "?")     ; string
    (char-seq "}")))   ; blob

(define user-defined-typecode
  (as-string
    (sequence
      (zero-or-more
	(bind item
	      (char-in-range #x60 #x7C)))  ; [`-|]
      (bind item
	    (char-in-range #x40 #x5F)))))  ; [@-_]

(define typecode
  (sequence* ((_    (char-seq "/"))
	      (type (any-of
		      primitive-typecode
		      user-defined-typecode)))
    (result (list 'typecode type))))

(define regular-magnitude-specifier
  (sequence* ((prefix (zero-or-more
			(bind item
			      (char-in-range #x40 #x5F))))  ; [@-_]
	      (suffix (bind item
			    (char-in-range #x20 #x3F))))    ; [ -?]
    (result (decode-regular-magnitude
	      suffix
	      (fold decode-regular-magnitude 0 prefix)))))

(define complement-magnitude-specifier
  (sequence* ((prefix (zero-or-more
			(bind item
			      (char-in-range #x20 #x3F))))  ; [ -?]
	      (suffix (bind item
			    (char-in-range #x40 #x5F))))    ; [@-_]
    (result (decode-complement-magnitude
	      suffix
	      (fold decode-complement-magnitude 0 prefix)))))

(define hex-character
  (bind item
	(check-any
	  (char-in-range #x30 #x39)     ; [0-9]
	  (char-in-range #x41 #x46))))  ; [A-F]

(define hex-integer
  (sequence hex-character hex-character))

(define regular-integer
  (sequence* ((count regular-magnitude-specifier)
	      (hex   (repeated hex-integer count)))
    ; Disallow leading zeros.
    (let ((n (decode-regular-integer hex)))
      (if (or (= 0 (length hex)) (>= n (expt 256 (- (length hex) 1))))
	(result n)
	fail))))

(define non-zero-regular-integer
  (bind regular-integer
	(lambda (i)
	  (if (= 0 i)
	    fail
	    (result i)))))

(define non-zero-or-one-regular-integer
  (bind regular-integer
	(lambda (i)
	  (if (or (= 0 i) (= 1 i))
	    fail
	    (result i)))))

(define complement-integer
  (sequence* ((count complement-magnitude-specifier)
	      (hex   (repeated hex-integer count)))
    ; Disallow leading zeros.
    (let ((n (decode-complement-integer hex)))
      (if (or (= 0 (length hex)) (>= n (expt 256 (- (length hex) 1))))
	(result n)
	fail))))

(define non-zero-complement-integer
  (bind complement-integer
	(lambda (i)
	  (if (= 0 i)
	    fail
	    (result i)))))

(define non-zero-or-one-complement-integer
  (bind complement-integer
	(lambda (i)
	  (if (or (= 0 i) (= 1 i))
	    fail
	    (result i)))))

(define integer-terminator
  (sequence* ((_ (char-seq "\t")))
    (result '())))

(define integer-list
  (recursive-parser
    (any-of
      (sequence* ((n    non-zero-or-one-complement-integer)  ; non-zero-or-one-complement-integer '~'
		  (~    (char-seq "~")))
	(result `(,n)))
      (sequence* ((a    non-zero-complement-integer)         ; non-zero-complement-integer non-zero-or-one-regular-integer '\t'
		  (b    non-zero-or-one-regular-integer)
		  (_    (char-seq "\t")))
	(result `(,a ,b)))
      (sequence* ((a    non-zero-complement-integer)         ; non-zero-complement-integer non-zero-regular-integer integer-list
		  (b    non-zero-regular-integer)
		  (rest integer-list))
	(result `(,a ,b ,@rest))))))

(define negative-number
  (sequence* ((_         (char-seq "<"))
	      (whole     complement-integer)
	      (fractions (any-of
			   integer-terminator
			   integer-list)))
    (result (converge (- whole) fractions))))

(define positive-number
  (sequence* ((_         (char-seq ">"))
	      (whole     regular-integer)
	      (fractions (any-of
			   integer-terminator
			   integer-list)))
    (result (converge whole fractions))))

(define number
  (any-of
    negative-number
    positive-number))

(define printable-non-tab-char
  ; TODO: exclude the following codepoint ranges:
  ;  + C0 control codes except tab: U+0000 -> U+0008 and U+000A -> U+001F
  ;  + DEL: U+007F
  ;  + C1 control codes: U+0080 -> U+009F
  ;  + Unicode separators: U+2028, U+2029
  ;  + Language tags: U+E000 -> U+E007F ; Although see emoji caveat
  ;  + Interlinear annotations: U+FFF9, U+FFFA, U+FFFB
  (bind item
	(lambda (c)
	  (if (eqv? c #\tab)
	    fail
	    (result c)))))

(define escaped-utf-8
  (any-of
    (bind (char-seq "\t~")
	  (lambda (s)
	    (result "\t")))
    printable-non-tab-char))

(define string*
  (sequence* ((_     (char-seq "?"))
	      (chars (as-string
		       (zero-or-more escaped-utf-8)))
	      (_     (char-seq "\t")))
    (result chars)))

(define base64-char
  (any-of
    (char-seq "+")
    (char-seq "/")
    (bind item
	  (char-in-range #x41 #x5A))    ; [A-Z]
    (bind item
	  (char-in-range #x61 #x7A))    ; [a-z]
    (bind item
	  (char-in-range #x30 #x39))))  ; [0-9]

(define base64-last-word
  (any-of
    (sequence base64-char base64-char base64-char    (char-seq "="))
    (sequence base64-char base64-char (char-seq "=") (char-seq "="))))

(define base64-word
  (sequence base64-char base64-char base64-char base64-char))

(define base64-words
  (sequence* ((str (as-string
		     (sequence
		       (zero-or-more base64-word)
		       (maybe        base64-last-word)))))
    (result (string->blob (base64-decode str)))))

(define blob
  (sequence* ((_    (char-seq "}"))
	      (data (maybe base64-words))
	      (_    (char-seq "\t")))
    (result data)))

(define user-defined-type
  (sequence* ((type     user-defined-typecode)
	      (contents (maybe keys '()))
	      (_        (char-seq "\t")))
    (result (cons (list 'typecode type) contents))))

(define primitive
  (any-of
    void*
    boolean
    typecode
    number
    string*
    blob))

; Read the first key from the input and leave the rest.
(define key
  (any-of
    primitive
    user-defined-type))

; Read all the keys until the end of the input.
(define keys
  (recursive-parser
    (one-or-more key)))

