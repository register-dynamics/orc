;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; orc-rsf - Register Serialisation Format tools in CHICKEN.
;;;
;;; gov.uk Open Registers are a way of expressing an authoritative list that
;;; you can trust.
;;;
;;; orc is an implementation of the Register data model, allowing users to
;;; wield and manipulate Registers as domain objects in their programs. We aim
;;; to support all the features of the model, including indexes, streaming
;;; updates, environments and cryptographic proofs.
;;;
;;; orc-rsf is a set of tools that allow users to dump & load Registers and
;;; parts of Registers so that they can move their data from place to place,
;;; either via files, streams or APIs.
;;;
;;;
;;;  Copyright (C) 2018-2019, Andy Bennett, Register Dynamics Limited.
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
;;; Andy Bennett <andyjpb@register-dynamics.co.uk>, 2018/06/20
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module orc-rsf
	(; RSF Input
	 read-rsf

	 ; RSF Output
	 write-rsf
	 )

(import chicken scheme)

; Units - http://api.call-cc.org/doc/chicken/language
(use extras data-structures srfi-1 ports)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(require-extension utf8)
(use srfi-19 message-digest sha2 blob-hexadecimal utf8-srfi-13 orc)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helpers

;; Operations on Dates

(define (string->date* src . fmtstr)
  (parameterize ((local-timezone-locale (utc-timezone-locale)))
		(apply string->date src fmtstr)))

(define (blob->digest blob #!optional (algo 'sha-256))

  (assert (or (string? blob)
	      (blob? blob))
	  (conc "blob->digest: blob argument must be a string or blob! We got " blob))

  (assert (eqv? 'sha-256 algo)
	  (conc "blob->digest: Only 'sha-256 item digest algorithms are supported! We got " algo))

  (let ((digest ((cond
		   ((string? blob) message-digest-string)
		   ((blob?   blob) message-digest-blob))
		 (sha256-primitive)
		 blob
		 'blob)))

    digest))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Item State Tracking

; A mapping between digest blobs and items that have been seen in the current
; rsf file.
(define current-items
  (make-parameter '()))

; Returns the item but not the line-no
(define (current-items-ref digest)
 (car
  (alist-ref digest (current-items) equal? '(#f . #f))))

; Overwrites item if it already exists. Therefore we cannot detect duplicate
; `add-item` lines in the RSF.
(define (current-items-add! digest item line-no)
  (current-items
    (alist-update!
      digest
      (cons item line-no)
      (current-items)
      equal?)))

; Calls proc with the digest, item and the line-no for each item in
; current-items.
(define (current-items-for-each proc)
  (for-each
    (lambda (digest+item)
      (let ((digest  (car  digest+item))
	    (item    (cadr digest+item))
	    (line-no (cddr digest+item)))
	(proc digest item line-no)))
    (current-items)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; RSF (Register Serialisation Format) parser and stream operations

;; Stream command handlers

(define (rsf-assert-root-digest line-no register digest)
  ; deconstrucut the sha-256:xxxx thing
  ; check that the digest-algorithm matches or is available
  ; check that the hash matches
  (fprintf (current-error-port) "~A: rsf-assert-root-digest: ~A\n" line-no digest)
  register)

(define (rsf-add-item line-no register item)
  (let ((digest (blob->digest item))
	(item   (make-item item)))
    (current-items-add! digest item line-no))
  register)

; A multi-valued append-entry looks like this:
; append-entry	user	UA	2016-10-21T16:11:20Z	sha-256:37ca110698ea569fc229e5042830384890ab1095737f1630c9de30692cfcf973;sha-256:0ed1f6d3321a473b463a17b46332fe920e853954db856844669303a5aba0361b
(define (rsf-append-entry line-no register region key timestamp item-refs)

  (assert (or (equal? "system" region)
	      (equal? "user"   region))
	  (conc "rsf-append-entry: Only 'system' and 'user' regions are supported! We got " region " on line " line-no))

  ; Convert "sha-256:abc123" to a blob.
  (define (string->digest str)
    (let ((parts (string-split str ":" #t)))

      (assert (= 2 (length parts))
	      (conc "rsf-append-entry: string->digest got an item reference with more than 2 parts on line " line-no ": " str))

      (assert (equal? "sha-256" (car parts))
	      (conc "rsf-append-entry: string->digest got an item reference with an unsupported digest type on line " line-no ": " (car parts)))

      (with-input-from-string  (conc "#${" (second parts) "}") read)))


  (let* ((item-refs (string-split item-refs ";" #t))
	 (items     (map
		      (lambda (item-ref)
			(let ((item (current-items-ref (string->digest item-ref))))
			  (assert item
				  (conc "rsf-append-entry: Cannot resolve reference to item " item-ref " on line " line-no))
			  item))
		      item-refs))
	 (entry     (apply make-entry
			   (string->symbol region)
			   (make-key key)
			   (string->date* timestamp "~Y-~m-~dT~H:~M:~SZ")
			   items)))
    (register-append-entry register entry)))


;; Parser

(define commands
  `(("assert-root-hash" . ,rsf-assert-root-digest)
    ("add-item"         . ,rsf-add-item)
    ("append-entry"     . ,rsf-append-entry)))

(define (command->proc command)
  (alist-ref command commands equal? values))

; Reads RSF from (current-input-port) and puts it in a Register.
(define (read-rsf #!optional name register)

  (assert (or (eq? #f register) (register? register))
	  (conc "read-rsf: register argument must be a register! We got " register))

  (with-register-transaction
    (lambda ()
      (parameterize ((current-items '()))
	(let loop
	  ((register      (or register (make-register name)))
	   (previous-line #f)
	   (line          (read-line))
	   (line-no       1))

	  (assert (register? register)
		  (conc "read-rsf: The handler for line " (sub1 line-no) " returned " register " which is not a register!"))

	  (cond
	    ((eof-object? line)
	     (if (not (equal? "assert-root-hash" (car (string-split previous-line "\t" #t))))
	       (fprintf (current-error-port) "WARNING: RSF file did not end with assert-root-hash! Integrity cannot be confirmed.\n"))
	     (current-items-for-each
	       (lambda (digest item line-no)
		 (if (not (item-item-ref item))
		   (fprintf (current-error-port) "WARNING: Item on line ~A with digest ~A was never referenced by an entry: ~A\n" line-no digest item))))
	     register)
	    (else
	      (loop
		(let* ((commands (string-split line "\t" #t))
		       (command  (car commands))
		       (rest     (cdr commands)))

		  (if (= 1 line-no)
		    ; First line *must* be an assert-root-hash
		    (assert (equal? "assert-root-hash" command)
			    (conc "read-rsf: RSF files must begin with assert-root-hash! We got " line " on line " line-no)))

		  (apply (command->proc command) line-no register rest))
		line
		(read-line)
		(add1 line-no)))))))))


;; Emitter

; Takes entries from a Register and writes RSF to (current-output-port).
(define (write-rsf register #!optional (start 0) (end (register-version register)))

  ; Emit the `assert-root-hash`.
  (printf "assert-root-hash\tsha-256:~A\n" (blob->hex (register-root-digest register start)))

  (parameterize ((current-items '()))
    (for-each
      (lambda (entry)

	(let ((digests
		; Emit the `add-item`s where necessary.
		(fold
		  (lambda (item seed)
		    (let ((digest (blob->digest (item-blob item))))
		      (if (not (current-items-ref digest))
			(begin
			  (current-items-add! digest item 0)
			  (printf "add-item\t~A\n" (item-blob item)))) ; TODO: assert no tabs
		      (cons
			(conc "sha-256:" (blob->hex digest))
			seed)))
		  '()
		  (entry-items entry))))

	  ; Emit the `append-entry`.
	  (printf
	    "append-entry\t~A\t~A\t~A\t~A\n"
	    (entry-region entry)
	    (key->string (entry-key entry))  ; TODO: escape tabs
	    (date->string (entry-ts entry) "~Y-~m-~dT~H:~M:~SZ")
	    (string-join digests ","))))     ; TODO: sort the items

      (register-entries-range register start end))

    ; Emit the `assert-root-hash`.
    (printf "assert-root-hash\tsha-256:~A\n" (blob->hex (register-root-digest register end)))))


)

