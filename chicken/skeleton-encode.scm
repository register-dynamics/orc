;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; skeleton-encode - serialisation routines for Register Key data
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
;;; Andy Bennett <andyjpb@register-dynamics.co.uk>, 2019/01/09
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import chicken scheme)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use numbers utf8-srfi-13 matchable base64)


;;;;;;;;;;
;;; Helpers

(define (skeleton-encode-abort . x)
  (fprintf (current-error-port) "\nSkeleton (Encode) Aborting!\n\n")
  (apply abort x))



;;;;;;;;;;
;;; Serialisers

;; void

(define (void? k)
  (eq? (void) k))

(define (write-void k)
  (write-char #\!))


;; boolean

(define (false? k)
  (eq? #f k))

(define (write-false k)
  (write-char #\$))

(define (true? k)
  (eq? #t k))

(define (write-true k)
  (write-char #\%))


;; typecode

(define (primitive-typecode? t)
  (and
    (parse (sequence primitive-typecode end-of-input) t)
    #t))

(define (user-defined-typecode? t)
  (and
    (parse (sequence user-defined-typecode end-of-input) t)
    #t))

(define (typecode? k)
  (match k
    (('typecode t)
     (or
       (primitive-typecode?    t)
       (user-defined-typecode? t)))
    (else #f)))

(define (write-typecode k)
  (printf "/~A" (second k)))


;; number
; We check that the number is a type of number that skeleton can represent in
; its primitive number type. If it is not then we abort. This means that if the
; user wants to supply a serialiser for other types of number then their
; predicate must appear earlier that this predicate in the unparsers list.
(define (number*? k)
  (if (number? k)
    (cond
      ((integer?  k) #t)
      ((rational? k) #t)
      (else
	(skeleton-encode-abort (conc k " is a type of number that we don't support. Skeleton's primitive types can only handle integers or rationals."))))
    #f))

; n *MUST* be exact: this is not guranteed to terminate when using the floating
; point maths routines!
(define (continued-fraction n terms)
  (let* ((whole (floor n))
	 (frac  (- n whole)))
    ;(printf "n: ~A, w: ~A, f: ~A\n" n whole frac)
    (if (= 0 frac)
      (reverse (cons whole terms))
      (continued-fraction
	(/ (denominator frac) (numerator frac))
	(cons whole terms)))))

; Converts a number into (uppercase) hexadecimal and ensures that the number of
; characters returned is a multiple of the 'm' argument.
(define (number->hex i m)
  (let* ((s       (number->string i 16))
	 (padding (make-string
		    (modulo (- m (string-length s)) m)
		    #\0))
	 (s       (string-append padding s)))
    (string-upcase! s)))

; Convert a number into a list of integers that each contain 5 bits worth of
; data from the number.
; We deliberately don't call `reverse` on the output from `string-fold` (and,
; therefore, we return the list "backwards") because the callers always treat
; the last value specially so it's easiest for them if it's on the front of the
; list.
; We go to some lengths here to not make assumptions about the size of 'm'.
; This means that we can't use the bitwise-* or arithmetic-shift procedures on
; m directly.
(define (integer->5bit-list m)
  (let* ((m (number->hex m 5)) ; Convert m to a string of hexadecimal digits.
	 (l (string-fold ; Process each (4bit) hexadecimal digit in turn to produce 5bit integers.
	      (lambda (c s) ; c is the next hex character.
		(match s  ; s is '((<number-of-remaining-bits> . <remaining-bits>) . <5bit-list>)
		  (((n . b) . l)
		   (let* ((c (char->integer c))
			  (c (if (> c #x39)   ; c > '9' => in [A-F]
			       (- c #x37)     ; Return c - 'A' - 10
			       (- c #x30))))  ; Return c - '0'
		     (if (< n 1) ; We don't have enough bits to emit anything this time.
		       `((4 . ,c) . ,l)
		       (let* ((n-used (- 5 n)) ; The number of bits of c we are going to consume now.
			      (c-mask (bitwise-and
					#xF
					(arithmetic-shift #xF (- 4 n-used))))
			      (c*      (arithmetic-shift
					 (bitwise-and c-mask c)
					 (- (- 4 n-used))))
			      (b-mask (- (expt 2 n) 1)) ; The bits of b we are going to consume now
			      (b      (arithmetic-shift
					(bitwise-and b-mask b)
					n-used))
			      (i ; Combine the bits in the accumulator 'b' with the bits from the char 'c'.
				(bitwise-ior c* b)))
			 (if (and (null? l) (= 0 i)) ; Don't include leading zeros.
			   `((,(- 4 n-used) . ,c) . ,l)
			   `((,(- 4 n-used) . ,c) . ,(cons i l)))))))))
	      '((0 . 0) . ())
	      m)))
    (if (null? (cdr l)) ; Return the 5bit-list.
      '(0)
      (cdr l))))

(define (write-regular-magnitude-specifier m)
  (let* ((m (integer->5bit-list m))
	 (m0 (car m))  ; The last 5 bits
	 (m+ (cdr m))) ; The rest of the bits
    (for-each
      (lambda (m)
	(display (integer->char (+ 64 m))))
      (reverse m+))
    (display (integer->char (+ 32 m0)))))

(define (write-complement-magnitude-specifier m)
  (let* ((m (integer->5bit-list m))
	 (m0 (car m))  ; The last 5 bits
	 (m+ (cdr m))) ; The rest of the bits
    (for-each
      (lambda (m)
	(display (integer->char (- 64 m))))  ; 32 - m + 64 - 32
      (reverse m+))
    (display (integer->char (- 96 m0)))))    ; 32 - m0 + 64

(define (write-regular-integer i)
  (if (= 0 i)
    (write-regular-magnitude-specifier 0)
    (let* ((s (number->hex i 2))
	   (m (/ (string-length s) 2)))
      (write-regular-magnitude-specifier m)
      (display s))))

(define (write-complement-integer i)
  (let* ((s (number->hex (- i 1) 2))
	 (m (/ (string-length s) 2))
	 (s (string-map!
	      (lambda (c)
		(let* ((c (char->integer c))
		       (c (if (and (>= c #x36) (<= c #x39))  ; '6' <= c <= '9' => complement in [6-9].
			    (- #x6F c)     ; Return '6' + '9' - c
			    (- #x76 c))))  ; Return 'F' + '0' - c
		  (integer->char c)))
	      s)))
    (write-complement-magnitude-specifier m)
    (display s)))

(define (write-integer-list l
			    #!optional
			    (terminator (if (odd? (length l)) #\~ #\tab))
			    (writer     write-complement-integer))
  (if (null? l)
    (write-char terminator)
    (begin
      (writer (car l))
      (write-integer-list
	(cdr l)
	terminator
	(if (eq? writer write-complement-integer)
	  write-regular-integer
	  write-complement-integer)))))

(define (write-negative-number k)
  (let* ((k (if (inexact? k) (inexact->exact k) k))
	 (n (continued-fraction k '())))
    (write-char #\<)
    (write-complement-integer (- (car n)))
    (if (= 1 (length n))
      (write-char #\tab)
      (write-integer-list (cdr n)))))

(define (write-positive-number k)
  (let* ((k (if (inexact? k) (inexact->exact k) k))
	 (n (continued-fraction k '())))
    (write-char #\>)
    (write-regular-integer (car n))
    (if (= 1 (length n))
      (write-char #\tab)
      (write-integer-list (cdr n)))))

(define (write-number* k)
  (if (< k 0)
    (write-negative-number k)
    (write-positive-number k)))


;; user defined type

(define (usertype? k)
  (match k
    ((('typecode t) . rest)
     (user-defined-typecode? t))
    (else #f)))

(define (write-usertype* k)
  (match k
    ((('typecode t) . rest)
     (display t)
     ; If the application of skeleton-encode aborts then the output stream is
     ; left in an inconsistent state because we've already written the typecode
     ; and will never write the terminator.
     (apply skeleton-encode rest)
     (write-char #\tab))))


;; string
; We don't check that the string doesn't have forbidden characters here in the
; predicate because then we'd have to loop over the string twice. This means
; that if the user wants to supply their own string unparser then they have to
; make provisions to serialise the primitive strings as well.
(define string*? string?)

(define (write-string* k)
  (write-char #\?)
  (string-for-each
    (lambda (c)
      (if (eqv? #\tab c)
	(begin
	  (write-char c)
	  (write-char #\~))
	(write-char c)))
    k)
  (write-char #\tab))


;; blob
(define blob*? blob?)

(define (write-blob* k)
  (write-char #\})
  (base64-encode (blob->string k) (current-output-port))
  (write-char #\tab))


; An alist that maps predicate functions to emitter functions. When a key or
; part of a key is to be written, the predicates are tried in order until one
; returns #t. The key (or part) is passed to the corresponding emitter function
; which is expected to write its skeleton representation to
; (current-output-port).
(define skeleton-unparsers
  (make-parameter
    `((,void?     . ,write-void)
      (,false?    . ,write-false)
      (,true?     . ,write-true)
      (,typecode? . ,write-typecode)
      (,number*?  . ,write-number*)
      (,string*?  . ,write-string*)
      (,usertype? . ,write-usertype*)
      (,blob*?    . ,write-blob*))))

; Write the supplied keys to the stdout.
(define (skeleton-encode . keys)
  (for-each
    (lambda (key)
      (let ((emitter (find
		       (lambda (pred)
			 ((car pred) key))
		       (skeleton-unparsers))))
	(if emitter
	  ((cdr emitter) key)
	  (skeleton-encode-abort (conc "We don't know how to serialise " key)))))
    keys))

