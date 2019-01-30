;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; orc - gov.uk Register Model in CHICKEN.
;;;
;;; gov.uk Open Registers are a way of expressing an authoritative list that
;;; you can trust.
;;;
;;; orc is an implementation of the Register data model, allowing users to
;;; wield and manipulate Registers as domain objects in their programs. We aim
;;; to support all the features of the model, including indexes, streaming
;;; updates, environments and cryptographic proofs.
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

(module orc
	(; Environments
	 ;make-environment
	 environment?
	 current-environment

	 ; Registers
	 make-register
	 open-register
	 list-registers
	 register?
	 register-root-digest
	 register-append-entry
	 register-records
	 register-records-range
	 register-record-ref

	 ; constructor
	 ; predicates
	 ; accessors
	 ; operations

	 make-key
	 string->key
	 key->string
	 key?
	 key-equal?
	 key<?
	 key<=?
	 key>?
	 key>=?
	 make-entry
	 entry?
	 entry-region
	 entry-key
	 entry-ts
	 entry-items
	 entry-audit-path
	 entry-audit-path*
	 make-item
	 item?
	 item-ref?
	 item-eqv?
	 item-equal?
	 item-item-ref
	 item-blob
	 item-ref?
	 item-or-ref?
	 item-ref-equal?
	 item-ref-evict

	 ; RSF
	 read-rsf

	 ; Backing Stores
	 open-backing-store
	 initialise-backing-store
	 with-backing-store
	 )


(import chicken scheme)

; Units - http://api.call-cc.org/doc/chicken/language
(use extras data-structures srfi-1 ports)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use srfi-19 message-digest sha2 sql-de-lite merkle-tree)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Macros

; Replace define with define-in-transaction to ensure that the whole procedure
; is run inside a database transaction.
; This is for the use of exported API procedures only.
; When those APIs are called from outside the module it ensures that they are
; wrapped in a non-nestable transaction. This ensures that the database is
; committed and therefore, any objects that are returned to the caller are
; persistent.
; When those APIs are called from within the module it ensures that there is
; already a transaction present and then wraps them in a nestable transaction
; to ensure that they are atomic.
(define internal-call? (make-parameter #f))
(define-syntax define-in-transaction
  (syntax-rules ()
		((define-in-transaction signature exp exp* ...)
		 (define signature
		   (assert (db-ctx) (conc "define-in-transaction: Calls to API procedures must be in the dynamic scope of a valid backing-store. You need to call `with-backing-store` in the correct place!"))
		   (let ((body (lambda () exp exp* ...)))
		     (if (internal-call?)
		       (begin
			 (assert (eq? #f (autocommit? (db-ctx)))
				 (conc "define-in-transaction: Internal calls to API procedures must already be inside a transaction by we are not!"))
			 (with-savepoint-transaction
			   (db-ctx)
			   body))
		       (parameterize ((internal-call? #t))
				     (with-transaction
				       (db-ctx)
				       body))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ADTs

;; environment
(define (make-environment)
  `(environment))

(define (environment? obj)
  (and
    (list? obj)
    (= 1 (length obj))
    (eqv? 'obj (car obj))))


;; register

; Allocates a new Register
(define-in-transaction (make-register #!optional name)

  (assert name
	  (conc "make-register: name argument must not be #f as we don't yet support non-persistent Registers!"))

  (let* ((log-id  (register-store-add! #f name))
	 (version 0))

    ; we need a symbol that tells us the item-format. i.e. json. better still, a validator!
    ;	should be in terms of region perhaps as system could use non-json or something?

    (create-register log-id version)))

; Create a register object from a reference to the backing store some version
; numbers.
;
; backing-store-ref
;   This is an opaque reference that the Backing Store uses to locate the
;   Register data.
;
; version
;   This is the number of entries in the Register's log that this instantiation
;   of the register will consider.
;
(define (create-register backing-store-ref version)

  (assert backing-store-ref
	  (conc "create-register: backing-store-ref argument must be specified! We got " backing-store-ref))

  (assert (integer? version)
	  (conc "create-register: version argument must be an integer! We got " version))

  `(register ,backing-store-ref ,version))

(define (update-register register
			 #!key
			 (backing-store-ref (register-backing-store-ref register))
			 (version           (register-version           register)))
  (create-register backing-store-ref version))

(define (register? obj)
  (and
    (list? obj)
    (= 3 (length obj))
    (eqv? 'register (car obj))))

(define (register-backing-store-ref register)
  (assert (register? register)
	  (conc "register-backing-store-ref: register argument must be a register! We got " register))
  (second register))

(define (register-version register)
  (assert (register? register)
	  (conc "register-version: register argument must be a register! We got " register))
  (third register))


;; key

; The key type is for representing the data used in the key field of entries.
; We wrap things in an explicit type so that we can support typed and compound
; keys in the future.

(define (make-key . parts)

  (assert (every key-or-primitive? parts)
	  (conc "make-key: every key part must itself be a key or a primitive type! We got " parts))

  (assert (= 1 (length parts))
	  (conc "make-key: compound keys are not currently supported. We got " parts))

  `(key ,@parts))

(define (key? obj)
  (and
    (list? obj)
    (= 2 (length obj)) ; Whilst we do not support compound keys.
    (eqv? 'key (car obj))))

(define (key-or-primitive? obj)
  (or
    (string? obj)
    (key?    obj)))

(define (key-parts key)
  (assert (key? key)
	  (conc "key-parts: key argument must be a key! We got " key))
  (cdr key))


;; entry

; Allocates a new entry in memory and returns it.
; We don't take a reference to a register so we don't validate that the items
; (if specified by reference) are present. That's the job of
; register-append-entry.
(define (make-entry region key ts . items)

  (assert (symbol? region)
	  (conc "make-entry: region argument must be a symbol! We got " region))

  (assert (or (eqv? 'user region)
	      (eqv? 'system region))
	  (conc "make-entry: Only 'system and 'user regions are supported! We got " region))

  (assert (key? key)
	  (conc "make-entry: key argument must be a key! We got " key))

  (assert (date? ts)
	  (conc "make-entry: ts argument must be a date! We got " ts))

  (assert (every item-or-ref? items)
	  (conc "make-entry: items must all be items or item-refs! We got " items))

  `(entry ,region ,key ,ts ,items))

(define (update-entry entry
		      #!key
		      (region (entry-region entry))
		      (key    (entry-key    entry))
		      (ts     (entry-ts     entry))
		      (items  (entry-items  entry)))
  (apply make-entry region key ts items))

(define (entry? obj)
  (and
    (list? obj)
    (= 5 (length obj))
    (eqv? 'entry (car obj))))

(define (entry-region entry)
  (assert (entry? entry)
	  (conc "entry-region: entry argument must be an entry! We got " entry))
  (second entry))

(define (entry-key entry)
  (assert (entry? entry)
	  (conc "entry-key: entry argument must be an entry! We got " entry))
  (third entry))

(define (entry-ts entry)
  (assert (entry? entry)
	  (conc "entry-ts: entry argument must be an entry! We got " entry))
  (fourth entry))

(define (entry-items entry)
  (assert (entry? entry)
	  (conc "entry-items: entry argument must be an entry! We got " entry))
  (fifth entry))


;; item
(define (make-item blob #!optional opaque-ref)

  (assert (or (string? blob)
	      (blob? blob))
	  (conc "make-item: blob argument must be a string or blob! We got " blob))

  (assert (or (not opaque-ref) (item-ref? opaque-ref))
	  (conc "make-item: opaque-ref argument must be an item-ref or #f! We got " opaque-ref))

  `(item ,opaque-ref ,blob))

(define (item? obj)
  (and
    (list? obj)
    (= 3 (length obj))
    (eqv? 'item (car obj))))

(define item-item-ref
  (getter-with-setter
    (lambda (item)
      (assert (item? item)
	      (conc "item-item-ref: item argument must be an item! We got " item))
      (second item))
    (lambda (item x)
      (assert (internal-call?)
	      (conc "item-item-ref set!: External callers cannot set an item's item-ref!"))
      (set! (second item) x))))

(define (item-blob item)
  (assert (item? item)
	  (conc "item-blob: item argument must be an item! We got " item))
  (third item))


;; item-ref

; Makes an item-ref that points to the item directly in the Backing Store.
; This constructor should only be called by the Backing Store code.
(define (make-item-ref item-id)

  (assert (integer? item-id)
	  (conc "make-item-ref: item-id argument must be an integer! We got " item-id))

  `(item-ref ,item-id))

(define (item-ref? obj)
  (and
    (list? obj)
    (= 2 (length obj))
    (eqv? 'item-ref (car obj))))

(define (item-or-ref? obj)
  (or (item?     obj)
      (item-ref? obj)))

(define (item-ref-item-id item-ref)

  (assert (item-ref? item-ref)
	  (conc "item-ref-item-id: item-ref argument must be an item-ref! We got " item-ref))

  (second item-ref))

; Evict an item-ref so that users can put them in things like web forms and
; then compare them to other item-refs in a POST handler. The item-id is
; supposed to be entirely internal to the Backing Store and is not guranteed to
; be stable. Therefore we deliberately introduce a bit of instability so that
; users of the API don't come to rely on them.
(define item-ref-evict

  (let ((magic (random 65536)))

    (lambda (item-ref)

      (assert (item-ref? item-ref)
	      (conc "item-ref-opaque-evict: item-ref argument must be an item-ref! We got " item-ref))

      (number->string
	(bitwise-xor magic (item-ref-item-id item-ref))))))


;; Operations

;; Operations on Environments

(define current-environment
  (make-parameter (make-environment) environment?))


;; Operations on Registers

(define-in-transaction (open-register name #!optional version)

  (assert name
	  (conc "open-register: name argument cannot be #f for persistent Registers!"))

  (if version
    (assert (integer? version)
	    (conc "open-register: version argument must be an integer or #f! We got " version)))

  (let ((register (register-store-ref #f name)))
    (if register
      (cond
	((eqv? #f version)
	 ; We weren't asked for a specific version so return the latest.
	 register)
	((= version (register-version register))
	 ; We were asked for a specific version and it is the latest so return
	 ; what we were given.
	 register)
	((< version (register-version register))
	 ; We were asked for a specific version and it is earlier than the
	 ; latest so return that.
	 (update-register
	   register
	   version: version))
	(else
	  ; We were asked for a specific version that is newer than the latest
	  ; we have!
	  (assert #f
		  (conc "open-register: Register " name " was requested at version " version " but the latest version we found was " (register-version register)))))
      #f)))

; Returns a an alist of Registers mapping name string to register objects
(define-in-transaction (list-registers)
  (register-store-registers))

(define-in-transaction (register-root-digest register)

  (assert (register? register)
	  (conc "register-root-digest: register argument must be a register! We got " register))

  (let ((tree
	  (make-merkle-tree
	    sha256-primitive
	    (make-backing-store
	      store: #f
	      ref:   (lambda (n)
		       (receive (cleanup next) (entry-store-stream register (add1 n))
				(let ((v (->string (next))))
				  (cleanup)
				  v)))
	      update: #f
	      size:   (constantly (register-version register))
	      levels: (lambda ()
			(log2-pow2>=n (register-version register)))
	      count-leaves-in-range: (lambda (start end)
				       (assert (<= end (register-version register)))
				       (- end start))
	      default-leaf: #f))))

   (merkle-tree-hash tree)))


  ; FIXME: We don't currently have a merkle tree implmentation that we can use
  ; on our backing store so fake the root digest for now. We just need
  ; something that changes as the Register changes so return something based on
  ; the backing store-id and the version number.
;  (string->blob
;    (conc
;      (number->string (register-backing-store-ref register))
;      "root digest "
;      (number->string (register-version register)))))


; Adds the specified item to the item pool.
; This procedure adds full items. item-refs are not allowed. For that you need register-declare-item.
(define-in-transaction (register-add-item register item)

  (assert (register? register)
	  (conc "register-add-item: register argument must be a register. We got " register))

  (assert (item? item)
	  (conc "register-add-item: item argument must be an item. We got " item))

  (item-store-add! item) ; Add it to the Backing Store.
  register)

; An entry serialises to json like this:
; {"index-entry-number":"1","entry-number":"1","entry-timestamp":"2016-04-05T13:23:05Z","key":"SU","item-hash":["sha-256:e94c4a9ab00d951dadde848ee2c9fe51628b22ff2e0a88bff4cca6e4e6086d7a"]}
(define-in-transaction (register-append-entry register entry)

  (assert (register? register)
	  (conc "register-append-entry: register argument must be a register! We got " register))

  (assert (entry? entry)
	  (conc "register-append-entry: entry argument must be an entry! We got " entry))

  ; prepare the entry by ensuring that we have opaque item-refs in the item list
  ; pass it to entry-store add
  ; return the register that entry-store-add gives us
  (entry-store-add
    register
    (update-entry
      entry
      items: (map (lambda (obj)
		    (let ((item-ref (cond
					((item-ref? obj) obj)
					((item?     obj) (item-item-ref obj))
					(else
					  (assert #f
						  (conc "register-append-entry: Got unknown item-or-ref " obj " in item-list for entry " entry))))))

		      (assert item-ref ; This happens when the item isn't passed to register-add-item before appearing in an entry passed to register-append-entry.
			      (conc "register-append-entry: 'digest reference of item " obj " could not be resolved to an item in the current scope. Whilst processing entry " entry))

		      item-ref))
		  (entry-items entry)))))


; TODO: probably best to rework this as an iterator interface!
; Returns a list of entries.
; Returns the latest entry for every key in the register.
; Tombstones are not visible through this interface. i.e. If the latest entry
; for a particular key has no items then it will not appear at all in the
; result set.
(define-in-transaction (register-records register region)

  (assert (register? register)
	  (conc "register-records: register argument must be a register. We got " register))

  (assert (or (eqv? 'user   region)
	      (eqv? 'system region))
	  (conc "register-records: Only 'system and 'user regions are supported! We got " region))

  (receive (cleanup next) (entry-store-keys register region)
	   (let loop ((entry   (next))
		      (entries '()))
	     (if entry
	       (loop (next) (cons entry entries))
	       (begin
		 (cleanup)
		 (reverse entries))))))

; Returns a list of entries.
; Finds the latest entries the the keys that lie lexographically between
; key-from and key-to, inclusive.
; Tombstones are not visible through this interface. i.e. If the latest entry
; for a particular key has no items then it will not appear at all in the
; result set.
(define-in-transaction (register-records-range register region key-from key-to)

  (assert (register? register)
	  (conc "register-record-range: register argument must be a register. We got " register))

  (assert (or (eqv? 'user   region)
	      (eqv? 'system region))
	  (conc "register-record-range: Only 'system and 'user regions are supported! We got " region))

  (assert (key? key-from)
	  (conc "register-record-range: key-from argument must be a key. We got " key-from))

  (assert (key? key-to)
	  (conc "register-record-range: key-to argument must be a key. We got " key-to))

  (reverse
    (receive (cleanup next) (entry-store-key-ref register region key-from key-to)
      (let loop ((entries '()))
	(receive (entry entry-number) (next)
	  (if entry
	    (loop (cons entry entries))
	    (begin
	      (cleanup)
	      entries)))))))

; Returns the latest entry corresponding to the key or #f if there isn't one.
; Tombstones are not visible through this interface. i.e. If the latest entry
; for a particular key has no items then it will not appear at all in the
; result set.
(define-in-transaction (register-record-ref register region key)

  (assert (register? register)
	  (conc "register-record-ref: register argument must be a register. We got " register))

  (assert (or (eqv? 'user   region)
	      (eqv? 'system region))
	  (conc "register-record-ref: Only 'system and 'user regions are supported! We got " region))

  (assert (key? key)
	  (conc "register-record-ref: key argument must be a key. We got " key))

  (receive (cleanup next) (entry-store-key-ref register region key)
		(receive (entry entry-number) (next)
			(assert (not (next))
				(conc "register-record-ref: Expected a single entry but got >1"))
			(cleanup)

			(values entry entry-number))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Higher level and compound operations on ADTs

;; Operations on Keys

(define (key-equal? a b)

  (assert (key? a)
	  (conc "key-equal?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key-equal?: b argument must be a key! We got " b))

  (equal? a b))

(define (key<? a b)

  (assert (key? a)
	  (conc "key<?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key<?: b argument must be a key! We got " a))

  (map string<? (key-parts a) (key-parts b)))

(define (key<=? a b)

  (assert (key? a)
	  (conc "key<=?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key<=?: b argument must be a key! We got " a))

  (map string<=? (key-parts a) (key-parts b)))

(define (key>? a b)

  (assert (key? a)
	  (conc "key>?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key>?: b argument must be a key! We got " a))

  (map string>? (key-parts a) (key-parts b)))

(define (key>=? a b)

  (assert (key? a)
	  (conc "key>=?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key>=?: b argument must be a key! We got " a))

  (map string>=? (key-parts a) (key-parts b)))


;; Operations on Entrys

; Calculates the audit path for a given entry number,
; which is the extra hashes required to prove that this entry
; is in the log.
; Generate an audit path for an entry specified by entry number.
(define-in-transaction (entry-audit-path register entry-number)

  (assert (register? register)
	  (conc "entry-audit-path: register argument must be a register! We got " register))

  (assert (and (number? entry-number) (> entry-number 0))
	  (conc "entry-audit-path: entry-number argument must be a number > 0! We got " entry-number))

  (let ((tree
	  (make-merkle-tree
	    sha256-primitive
	    (make-backing-store
	      store: #f
	      ref:   (lambda (n)
		       (receive (cleanup next) (entry-store-stream register (add1 n))
				(let ((v (->string (next))))
				  (cleanup)
				  v)))
	      update: #f
	      size:   (constantly (register-version register))
	      levels: (lambda ()
			(log2-pow2>=n (register-version register)))
	      count-leaves-in-range: (lambda (start end)
				       (assert (<= end (register-version register)))
				       (- end start))
	      default-leaf: #f))))

    (let ((path (merkle-audit-path (- entry-number 1) tree)))
      (list entry-number (register-version register) path))))


; Generate an audit path for an entry specified by key.
(define-in-transaction (entry-audit-path* register region key)

  (assert (register? register)
	  (conc "entry-audit-path: register argument must be a register! We got " register))

  (assert (or (eqv? 'user   region)
	      (eqv? 'system region))
	  (conc "entry-audit-path: Only 'system and 'user regions are supported! We got " region))

  (assert (key? key)
	  (conc "entry-audit-path: key argument must be a key. We got " key))


  (receive (entry entry-number) (register-record-ref register region key)
    (entry-audit-path register entry-number)))


;; Operations on Items

; Compare items.
; They must be equivalent. i.e. they must contain the same blob but the
; references only have to match if both items have them.
(define (item-eqv? a b)

  (assert (item? a)
	  (conc "item-eqv?: a argument must be an item! We got " a))

  (assert (item? b)
	  (conc "item-eqv?: b argument must be an item! We got " b))

  (let ((ref-a (item-item-ref a))
	(ref-b (item-item-ref b)))
    (and
      (equal? (item-blob a) (item-blob b))
      (if (and ref-a ref-b) ; If the items have references then they must be equal.
	(item-ref-equal? ref-a ref-b)
	#t))))

; Compare items.
; They must be equal?. i.e. they must contain the same blob and the same
; reference.
(define (item-equal? a b)

  (assert (item? a)
	  (conc "item-equal?: a argument must be an item! We got " a))

  (assert (item? b)
	  (conc "item-equal?: b argument must be an item! We got " b))

  (equal? a b))

; Compare item-refs.
; They must be equal?. i.e. they must match exactly.
(define (item-ref-equal? a b)

  (assert (item-ref? a)
	  (conc "item-ref-equal?: a argument must be an item-ref! We got " a))

  (assert (item-ref? b)
	  (conc "item-ref-equal?: b argument must be an item-ref! We got " b))

  (equal? a b))

; Set an item's item-ref if it doesn't already have one.
; Returns the item.
(define (item-set-ref! item item-ref)

  (assert (item? item)
	  (conc "item-set-ref!: item argument must be an item! We got " item))

  (assert (item-ref? item-ref)
	  (conc "item-set-ref!: item-ref argument must be an item-ref! We got " item-ref))

  (assert (not (item-item-ref item))
	  (conc "item-set-ref!: item argument's item-ref must be #f! We got " (item-item-ref item)))

  (set! (item-item-ref item) item-ref)

  item)



;; Operations on Dates

(define (string->date* src . fmtstr)
  (parameterize ((local-timezone-locale (utc-timezone-locale)))
		(apply string->date src fmtstr)))



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
  (register-add-item register (make-item item))
  register)

; A multi-valued append-entry looks like this:
; append-entry	user	UA	2016-10-21T16:11:20Z	sha-256:37ca110698ea569fc229e5042830384890ab1095737f1630c9de30692cfcf973;sha-256:0ed1f6d3321a473b463a17b46332fe920e853954db856844669303a5aba0361b
(define (rsf-append-entry line-no register region key timestamp item-refs)

  (assert (or (equal? "system" region)
	      (equal? "user"   region))
	  (conc "rsf-append-entry: Only 'system' and 'user' regions are supported! We got " region " on line " line-no))

  ; Convert "sha-256:abc123" to an item-ref.
  (define (string->item-ref str)
    (let ((parts (string-split str ":" #t)))

      (assert (= 2 (length parts))
	      (conc "rsf-append-entry: string->item-ref got an item reference: with more than 2 parts: " str))

      (make-item-ref
	(string->symbol (first parts))
	(with-input-from-string  (conc "#${" (second parts) "}") read))))


  (let* ((item-refs (string-split item-refs ";" #t))
	 (item-refs (map string->item-ref item-refs))
	 (entry     (apply make-entry
			   (string->symbol region)
			   (make-key key)
			   (string->date* timestamp "~Y-~m-~dT~H:~M:~SZ")
			   item-refs)))
    (register-append-entry register entry)))


;; Parser

(define commands
  `(("assert-root-hash" . ,rsf-assert-root-digest)
    ("add-item"         . ,rsf-add-item)
    ("append-entry"     . ,rsf-append-entry)))

(define (command->proc command)
  (alist-ref command commands equal? values))

; Reads RSF from (current-input-port) and puts it in a Register.
(define-in-transaction (read-rsf #!optional name register)

  (assert (or (eq? #f register) (register? register))
	  (conc "read-rsf: register argument must be a register! We got " register))

  (parameterize ((current-items '()))
    (let loop
      ((register (or register (make-register name)))
       (previous-line #f)
       (line     (read-line))
       (line-no  1))

      (assert (register? register)
	      (conc "read-rsf: The handler for line " (sub1 line-no) " returned " register " which is not a register!"))

      (cond
	((eof-object? line)
	 (if (not (equal? "assert-root-hash" (car (string-split previous-line "\t" #t))))
	   (fprintf (current-error-port) "WARNING: RSF file did not end with assert-root-hash! Integrity cannot be confirmed.\n"))
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
	    (add1 line-no)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SQLite Backing Store

; Opens an SQLite Database.
;
; filename
;   Any of:
;     + A filename on disk for a fully persistent backing store.
;     + 'memory for a new database in memory, unique to this connection.
;     + 'temporary for a new temporary database on disk, visible only to this
;       connection.
;
;   'memory or 'temporary cannot be used in pools.
;
; If the file does not exist, one is created transparently.
;
; Returns a dabase object.
(define (open-backing-store filename)
  (open-database filename))


; Checks whether the database has an appropriate schema. Optionaly initialises
; or upgrades it if not.
; A completely uninitialised database is initialised to the latest version of
; the schema if the initialise argument is true.
; If the auto-upgrade argument is true then when an old version of the schema
; is found it is upgraded to the latest version. Otherwise, a warning is
; printed.
; If the database has the latest version of the schema by the end of this
; procedure then #t is returned. Otherwise #f is returned.
;
; We use the dynamic variable db-ctx to find the database to initialise so you
; will have to call this inside `with-backing-store`.
; We use `with-transaction` here rather than `define-in-transaction` so that we
; know we're always in our own, non-nestable, transaction and can be sure our
; changes commit.
;
; Returns #t if the database was successfully initialised, #f if the database
; remains on an old version of the schema and throws an exception otherwise.
;
; There is currently no provision for customising the table names or having
; more than one backing store per database.
(define ensure-backing-store
  (let* ((schemas '(("CREATE TABLE \"entry-items\" (\"log-id\"  NOT NULL , \"entry-number\"  NOT NULL , \"item-id\"  NOT NULL );"
		     "CREATE TABLE \"entrys\" (\"log-id\" INTEGER NOT NULL , \"entry-number\" INTEGER NOT NULL , \"region\" TEXT NOT NULL , \"key\" TEXT NOT NULL , \"timestamp\" INTEGER NOT NULL , PRIMARY KEY (\"log-id\", \"entry-number\"));"
		     "CREATE TABLE \"item-digests\" (\"item-id\" INTEGER NOT NULL , \"algorithm\" TEXT NOT NULL , \"digest\" BLOB NOT NULL , PRIMARY KEY (\"item-id\", \"algorithm\"));"
		     "CREATE TABLE \"items\" (\"item-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"blob\" BLOB NOT NULL  UNIQUE );"
		     "CREATE TABLE \"registers\" (\"log-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"index-of\" INTEGER NOT NULL , \"name\" TEXT NOT NULL );"
		     "CREATE INDEX \"entry-items-log-id-entry-number-item-id\" ON \"entry-items\" (\"log-id\" ASC, \"entry-number\" ASC, \"item-id\" ASC);"
		     "CREATE UNIQUE INDEX \"entrys-region-key-entry-number-log-id\" ON \"entrys\" ( \"region\" ASC, \"key\" ASC, \"entry-number\" ASC, \"log-id\" ASC);"
		     "CREATE UNIQUE INDEX \"item-digests-algorithm-digest\" ON \"item-digests\" (\"algorithm\" ASC, \"digest\" ASC);"
		     "CREATE UNIQUE INDEX \"registers-index-of-name\" ON \"registers\" (\"index-of\" ASC, \"name\" ASC);")
		    ("CREATE TABLE \"orc-schema-version\" (\"version\" INTEGER PRIMARY KEY  NOT NULL );"
		     "INSERT INTO \"orc-schema-version\" (\"version\") VALUES (2);")
		    ("DROP TABLE \"item-digests\";"
		     "UPDATE \"orc-schema-version\" SET \"version\" = 3;")
		     ))
	 (latest  (length schemas)))

    (lambda (#!key (initialise #f) (auto-upgrade #f))
      (let ((db (db-ctx)))
	(with-transaction
	  db
	  (lambda ()
	    (let ((schema-version (store-version)))
	      (let ((rv ; Be explicit about the fact we need to calculate a return value for with-transaction.
		      (cond
			((= schema-version latest)
			 #t)
			((> schema-version latest)
			 (abort (conc "ensure-backing-store: Backing Store is at version ~A but the latest we know that we understand is ~A\n"
				      schema-version latest)))
			((or auto-upgrade (and initialise (= 0 schema-version)))
			 (for-each
			   (lambda (upgrade)
			     (for-each
			       (lambda (q)
				 (exec
				   (sql db q)))
			       upgrade))
			   (drop schemas schema-version))
			 (fprintf (current-error-port)
				  "Backing Store upgraded from version ~A to version ~A.\n"
				  schema-version
				  latest)
			 #t)
			(else
			  (fprintf (current-error-port)
				   "WARNING: Backing Store is at version ~A but can be upgraded to version ~A. Some features may not be available until you run `(initialise-backing-store auto-upgrade: #t)`\n"
				   schema-version
				   latest)
			  #f))))
		rv))))))))

; Initialises a database with the appropriate schema.
; A completely uninitialised database is always initialised to the latest
; version of the schema.
; If the auto-upgrade argument is true then when an old version of the schema
; is found it is upgraded to the latest version. Otherwise, a warning is
; printed.
; If the database has the latest version of the schema by the end of this
; procedure then #t is returned. Otherwise #f is returned.
;
; Returns #t if the database was successfully initialised, #f if the database
; remains on an old version of the schema and throws an exception otherwise.
;
; There is currently no provision for customising the table names or having
; more than one backing store per database.
(define (initialise-backing-store #!key (auto-upgrade #f))
  (ensure-backing-store
    initialise: #t
    auto-upgrade: auto-upgrade))

(define db-ctx (make-parameter #f))

(define (with-backing-store db thunk)
  (parameterize ((db-ctx db))
		(ensure-backing-store)
		(thunk)))

;; ADTs for the Backing Store

; An SQL query.
; This collects the query string together with the appropriate serialisers and
; deserialisers for using it.
(define (make-query query-string argument-serialisers result-deserialisers)

  (assert (string? query-string)
	  (conc "make-query: query-string argument must be a string! We got " query-string))

  (assert (list? argument-serialisers)
	  (conc "make-query: argument-serialisers argument must be a list! We got " argument-serialisers))

  (assert (every procedure? argument-serialisers)
	  (conc "make-query: argument-serialisers argument must be a list of procedures! We got " argument-serialisers))

  (assert (list? result-deserialisers)
	  (conc "make-query: result-deserialisers argument must be a list! We got " result-deserialisers))

  (assert (every procedure? result-deserialisers)
	  (conc "make-query: result-deserialisers argument must be a list of procedures! We got " result-deserialisers))

  `(query ,query-string ,argument-serialisers ,result-deserialisers))

(define (query? obj)
  (and
    (list? obj)
    (= 4 (length obj))
    (eqv? 'query (car obj))))

(define (query-string query)
  (assert (query? query)
	  (conc "query-string: query argument must be a query! We got " query))
  (second query))

(define (query-argument-serialisers query)
  (assert (query? query)
	  (conc "query-argument-serialisers: query argument must be a query! We got " query))
  (third query))

(define (query-result-deserialisers query)
  (assert (query? query)
	  (conc "query-result-deserialisers: query argument must be a query! We got " query))
  (fourth query))


;; Serialisers, Deserialisers and Type Checkers

; Type Checker: Expects a blob and returns it.
(define (require-blob obj)
  (assert (blob? obj)
	  (conc "require-blob: obj argument must be a blob! We got " obj))
  obj)

; Type Checker: Expects a blob. If we get NULL then we return #f.
(define (require-blob-or-null obj)
  (if (null? obj)
    #f
    (require-blob obj)))

; Type Checker: Expects a blob or a string and returns it.
(define (require-blob-or-string obj)
  (assert (or (string? obj) (blob? obj))
	  (conc "require-blob-or-string: obj argument must be a blob or a string! We got " obj))
  obj)

; Type Checker: Expects a blob or a string. If we get NULL then we return #f
;               otherwise we return the blob or string.
(define (require-blob-string-or-null obj)
  (if (null? obj)
    #f
    (require-blob-or-string obj)))

; Type Checker: Expects an integer and returns it.
(define (require-integer obj)
  (assert (integer? obj)
	  (conc "require-integer: obj argument must be an integer! We got " obj))
  obj)

; Type Checker: Expects an integer. If we get NULL then we return #f otherwise
;               we return the integer.
(define (require-integer-or-null obj)
  (if (null? obj)
    #f
    (require-integer obj)))

; Type Checker: Expects an integer greater than zero and returns it.
(define (require-integer>0 obj)
  (assert (integer? obj)
	  (conc "require-integer>0: obj argument must be an integer! We got " obj))
  (assert (> obj 0)
	  (conc "require-integer>0: obj argument must be an integer greater than 0! We got " obj))
  obj)

; Serialiser: Converts #f to 0 and expects a positive integer otherwise.
(define (positive-integer-or-false->integer obj)
  (cond
    ((integer? obj)
     (assert (> obj 0)
	     (conc "integer-or-false->integer: obj argument must be an integer greater than 0 or #f! We got " obj))
     obj)
    ((eqv? #f obj)  0)
    (else
      (assert #f
	      (conc "integer-or-false->integer: obj argument must be an integer of #f! We got " obj)))))

; Deserialiser: Converts 0 to #f and expects a positive integer otherwise.
(define (positive-integer-or-zero->integer-or-false obj)
  (if (integer? obj)
    (cond
      ((= 0 obj) #f)
      ((> obj 0) obj)
      (else
	(assert #f
		(conc "positive-integer-or-zero->integer-or-false: obj argument must be an integer greater than or equal to 0. We got " obj))))
    (assert #f
	    (conc "positive-integer-or-zero->integer-or-false: obj argument must be an integer greater than or equal to 0. We got " obj))))

; Deserialiser: Converts NULL to 0 and expects a positive integer otherwise
(define (null-or-positive-integer->integer obj)
  (cond
    ((null? obj) 0)
    ((integer? obj)
     (assert (> obj 0)
	     (conc "null-or-positive-integer->integer: obj argument must be an integer greater than 0 or '()! We got " obj))
     obj)
    (else
      (assert #f
	      (conc "null-or-positive-integer->integer: obj argument must be an integer or '()! We got " obj)))))

; Type Checker: Expects a string and returns it.
(define (require-string obj)
  (assert (string? obj)
	  (conc "require-string: obj argument must be a string! We got " obj))
  obj)

; Type Checker: Expects a string. If we get NULL then we return #f otherwise we
;               return the string
;(define (require-string-or-null obj)
;  (if (null? obj)
;    #f
;    (require-string obj)))

; Serialiser: Converts a key to a string with nice lexical semantics.
; The lexical semantics are such that the returned string sorts in the order
; that one would expect the original keys to sort in.
(define (key->string key)
  (assert (key? key)
	  (conc "key->string: key argument must be a key! We got " key))
  (let ((parts (key-parts key)))
    (assert (= 1 (length parts))
	    (conc "key->string: Keys with not exactly one part are not currently supported! We got " key))
    (let ((part (car parts)))
      (assert (string? part)
	      (conc "key->string: Keys with non-string parts are not currently supported! We got " key))
      part)))

; Deserialiser: Converts a string with nice lexical semantics to a key.
(define (string->key str)
  (assert (string? str)
	  (conc "string->key: str argument must be a string! We got " str))
  (make-key str))

; Serialiser: Converts an srfi-19 date to a UNIX style epoch-indexed integer.
; obj must represent a date in UTC so that we don't have to worry about
; conversion of future dates; we can let the user do that for now!.
(define (date->integer obj)
  (assert (date? obj)
	  (conc "date->integer: obj argument must be an srfi-19 date! We got " obj))
  (assert (equal? "UTC" (date-zone-name obj))
	  (conc "date->integer: obj argument must represent a date in UTC! We got " obj))
  (string->number (format-date "~s" obj))) ; (time->seconds (date->time-utc obj)) ; Note that time->seconds can return a ratnum!

; Deserialiser: Converts a UNIX style epoch-index integer to an srfi-19 date.
(define (integer->date obj)
  (assert (integer? obj)
	  (conc "integer->date: obj argument must be an integer! We got " obj))
  (parameterize ((local-timezone-locale (utc-timezone-locale)))
		(seconds->date obj)))


;; Operations for the Backing Store

; Run a query on the backing store, applying the serialisers, deserialisers and
; constructors at the appropriate time.
(define (run-query db the-query constructor . arguments)

  (assert (query? the-query)
	  (conc "run-query: query argument must be a query! We got " the-query))

  (assert (procedure? constructor)
	  (conc "run-query: constructor argument must be a procedure! We got " constructor))

  (apply query
	 (map-rows
	   (lambda (row)
	     (let ((row
		     (map
		       (lambda (proc col)
			 (proc col))
		       (query-result-deserialisers the-query)
		       row)))
	       (apply constructor row))))
	 (sql db (query-string the-query))
	 (map
	   (lambda (proc arg)
	     (proc arg))
	   (query-argument-serialisers the-query)
	   arguments)))

; Manage running a query on the backing store, applying the serialisers,
; deserialises and constructors at the appropriate time.
; This procedure does not run the query itself but provides the caller with a
; pair of procedures: one for cleanup and an iterator. Calling the iterator
; will yield the next row from the result set. The cleanup procedure must be
; called when the caller is done with the query whether or not they exhaust all
; the rows in the result set.
; The return values of this procedure must not be passed over a transaction
; boundary so things that call it directly must not use lambda-in-savepoint or
; define-in-transaction and things that receive the resulting procedures must
; be careful in their use of transactions.
(define (stream-query db the-query constructor . arguments)

  (assert (query? the-query)
	  (conc "stream-query: query argument must be a query! We got " the-query))

  (assert (procedure? constructor)
	  (conc "stream-query: constructor argument must be a procedure! We got " constructor))

  (let ((caller '_)) ; The continuation of the person that calls the iterator so we can return to them.
    (letrec ((orig-cleanup
	       (lambda ()
		 #f))
	     (cleanup ; The procedure that will allow us to exit without consuming all the rows.
	       orig-cleanup)

	     (next-row
	       (lambda ()
		 (apply query

			(lambda (s)
			  ; call fetch for each row
			  (let ((row
				  (call/cc
				    (lambda (rest-of-results)
				      (set! next-row (lambda ()
						       (rest-of-results (fetch s))))
				      (set! cleanup  (lambda ()
						       ; Fake the end of the result set so that we fall out the bottom of (apply query ...)
						       ; We don't actually do any work here other than make the sql-de-lite stuff finalize.
						       ; All the real cleanup is done in the code that lexographically follows (apply
						       ; query ...).
						       ; If more logic is put here, the approach to (set! cleanup orig-cleanup) below might
						       ; have to change.
						       (rest-of-results '())))

				      (fetch s)))))


			    (if (not (null? row))
			      ; If there was a row, deserialise it, construct it and return it to the caller
			      ; of the iterator by jumping to their continuation, if not fall out the bottom
			      ; of (apply query ...) thus tidying up the database
			      (caller
				(apply
				  constructor
				  (map
				    (lambda (proc col)
				      (proc col))
				    (query-result-deserialisers the-query)
				    row))))

			    ; Reset the cleanup procedure: We're going to cleanup right after (apply query ...) finishes,
			    ; but the user might still call us anyway.
			    ; This is not strictly necessary but, it is semantically more correct than letting the user
			    ; call the other cleanup procedure. If it is called, it saves us the effort of falling out of
			    ; the bottom of (apply query ...) again.
			    ; We don't do the same for next-row because we want the user to get the "operation on
			    ; finalized statement" error that results from calling it after cleanup.
			    (set! cleanup orig-cleanup)

			    'never-seen))

			(sql db (query-string the-query))
			(map
			  (lambda (proc arg)
			    (proc arg))
			  (query-argument-serialisers the-query)
			  arguments))

			  (caller 'no-more-rows)))) ; Returns 'cleaned up to the correct caller, however we got here.

      (values ; Return a cleanup procedure and an iterator procedure to the caller of stream-query
	(lambda () ; The cleanup procedure: start with a dummy one until we start doing things to the database.
	  (call/cc
	    (lambda (k)
	      (set! caller k)
	      (cleanup))))
	(lambda () ; The iterator. Each call to this will get the next row from the database.
	  (call/cc
	    (lambda (k)
	      (set! caller k)
	      (next-row))))))))

; Run an exec on the backing store, applying the serialisers at the appropriate
; time.
; Statements that are exec'd rather than query'd don't return a result set so
; we don't need to run the deserialisers or constructors.
(define (run-exec db the-query . arguments)

  (assert (query? the-query)
	  (conc "run-query: query argument must be a query! We got " the-query))

  (apply exec
	 (sql db (query-string the-query))
	 (map
	   (lambda (proc arg)
	     (proc arg))
	   (query-argument-serialisers the-query)
	   arguments)))

(define (<=1-result results)
  (case (length results)
    ((0) #f)
    ((1) (car results))
    (else
      (assert #f
	      (conc "<=1-result: Expected one result! We got " results)))))

; Replace lambda with lambda-in-savepoint to ensure that the whole procedure
; is run inside a database savepoint transaction.
; This is for the use of the Backing Store procedures only. It wraps calls to
; Backing Store procedures in a savepoint transaction to ensure that they are
; atomic but the Backing Store interface requires that we are already inside a
; existing transaction so that the orc operations as a whole are transactional.
(define-syntax lambda-in-savepoint
  (syntax-rules ()
		((lambda-in-savepoint args exp exp* ...)
		 ;(lambda args exp exp* ...))))
		 (lambda args
		   (assert (eq? #f (autocommit? (db-ctx)))
			   (conc "lambda-in-savepoint: Calls into the Backing Store expect to already be inside a transaction but we are not!"))
		   (with-savepoint-transaction
		     (db-ctx)
		     (lambda ()
		       exp exp* ...))))))


; Returns the version of the schema that the Backing Store is currently using.
(define store-version
  (lambda-in-savepoint ()
    (if (= 0 (length (query fetch-all (sql (db-ctx) "SELECT \"tbl_name\" FROM \"sqlite_master\" WHERE \"tbl_name\" = \"orc-schema-version\" AND \"type\" = \"table\";"))))
      (if (equal? (query fetch-all (sql (db-ctx) ; The original schema wasn't versioned so we have to compare it piece-by-piece.
#<<END
					SELECT "sql"
					FROM "sqlite_master"
					WHERE
					(("type" = "table"
					  AND
					  ("tbl_name" IN
					   ("entry-items", "entrys", "item-digests", "items", "registers")))
					 OR
					 ("type" = "index"
					  AND
					  ("tbl_name" IN
					   ("entrys", "item-digests", "items", "items", "registers", "entry-items", "entrys", "item-digests", "registers"))))
					ORDER BY "sql";
END
					))
		  '((()) (()) (()) (()) (()) ; The sqlite_autoindexes don't have any SQL. We could exclude them but counting them makes sure they're there!
			 ("CREATE INDEX \"entry-items-log-id-entry-number-item-id\" ON \"entry-items\" (\"log-id\" ASC, \"entry-number\" ASC, \"item-id\" ASC)")
			 ("CREATE TABLE \"entry-items\" (\"log-id\"  NOT NULL , \"entry-number\"  NOT NULL , \"item-id\"  NOT NULL )")
			 ("CREATE TABLE \"entrys\" (\"log-id\" INTEGER NOT NULL , \"entry-number\" INTEGER NOT NULL , \"region\" TEXT NOT NULL , \"key\" TEXT NOT NULL , \"timestamp\" INTEGER NOT NULL , PRIMARY KEY (\"log-id\", \"entry-number\"))")
			 ("CREATE TABLE \"item-digests\" (\"item-id\" INTEGER NOT NULL , \"algorithm\" TEXT NOT NULL , \"digest\" BLOB NOT NULL , PRIMARY KEY (\"item-id\", \"algorithm\"))")
			 ("CREATE TABLE \"items\" (\"item-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"blob\" BLOB NOT NULL  UNIQUE )")
			 ("CREATE TABLE \"registers\" (\"log-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"index-of\" INTEGER NOT NULL , \"name\" TEXT NOT NULL )")
			 ("CREATE UNIQUE INDEX \"entrys-region-key-entry-number-log-id\" ON \"entrys\" ( \"region\" ASC, \"key\" ASC, \"entry-number\" ASC, \"log-id\" ASC)")
			 ("CREATE UNIQUE INDEX \"item-digests-algorithm-digest\" ON \"item-digests\" (\"algorithm\" ASC, \"digest\" ASC)")
			 ("CREATE UNIQUE INDEX \"registers-index-of-name\" ON \"registers\" (\"index-of\" ASC, \"name\" ASC)")))
	1  ; We found the original schema
	0) ; Things haven't been initialised yet
      (let ((v (query fetch-all (sql (db-ctx) "SELECT \"version\" FROM \"orc-schema-version\";"))))
	(if (eq? 1 (length v))
	  (caar v)
	  (abort (conc "orc-schema-version table is corrupt. Expected one row but got " v)))))))


; Add an item to the Backing Store.
; Returns an item-ref if successful and throws an exception otherwise.
(define item-store-add!
  (let ((insert-item
	  (make-query
	    "INSERT INTO \"items\" (\"blob\") VALUES (?1);"
	    `(,require-blob-or-string) ; blob
	    `())))                     ; nothing

    (lambda-in-savepoint (item)

      (assert (item? item)
	      (conc "item-store-add!: item argument must be an item! We got " item))

      (let ((rows-changed (run-exec (db-ctx) insert-item (item-blob item)))
	    (item-id      (last-insert-rowid (db-ctx))))

	(assert (= 1 rows-changed)
		(conc "item-store-add!: Expected 1 row to change when INSERTing item into database. We got " rows-changed))

	(assert (item-item-ref item)
		(conc "item-store-add!: We currently only support items that already contain an item-ref. We got " item))

	; TODO: transactionalise / savepoint
	; TODO: if item already exists but ref does not, succeed so that we can
	;       add or migrate digests later.

	(make-item-ref item-id)))))


; Finds a Register in the Backing Store by name
; Returns a register object for the Register at the latest version or #f if the
; Register cannot be found.
(define register-store-ref
  (let ((select-register-by-name
	  (make-query
#<<END
	    SELECT
	    "registers"."log-id" AS "log-id",
	    MAX("entrys"."entry-number") AS "version"
	    FROM
	    "registers"

	    LEFT OUTER JOIN "entrys"
	    ON
	    "registers"."log-id" = "entrys"."log-id"

	    WHERE
	    "registers"."index-of" = ?1
	    AND "registers"."name" = ?2;
END
	    `(,positive-integer-or-false->integer ,require-string)            ; (index-of name)
	    `(,require-integer-or-null ,null-or-positive-integer->integer)))) ; (log-id version)
    ; we use require-integer-or-null to deserialise log-id because in the case where the name is not found we get a single row of NULLs in the Result Set

    (lambda-in-savepoint (index-of name)

      (define (->register log-id version)
	(if log-id
	  (create-register log-id version)
	  #f))

      (assert (or (eqv? #f index-of) (integer? index-of))
	      (conc "register-store-ref: index-of argument must be an integer or #f! We got " index-of))

      (assert (string? name)
	      (conc "register-store-ref: name argument must be a string! We got " name))

      (let ((registers (run-query (db-ctx) select-register-by-name ->register index-of name)))
	(<=1-result registers)))))

; Finds all the Registers that we know about.
; This returns an alist that maps name strings to register objects. The
; register objects are always opened at the latest version.
(define register-store-registers
  (let ((select-registers
	  (make-query
#<<END
	    SELECT
	    "registers"."log-id"         AS "log-id",
	    "registers"."index-of"       AS "index-of",
	    "registers"."name"           AS "name",
	    MAX("entrys"."entry-number") AS "version"

	    FROM
	    "registers"

	    LEFT OUTER JOIN "entrys"
	    ON
	    "registers"."log-id" = "entrys"."log-id"

	    WHERE
	    "registers"."index-of" = 0

	    GROUP BY "registers"."log-id";
END
	    `()
	    `(,require-integer ,positive-integer-or-zero->integer-or-false ,require-string ,null-or-positive-integer->integer)))) ; (log-id index-of name version)
    ; We use require-integer to deserialise the log-id because in the case where nothing is found, we get a Result Set of zero rows.

    (lambda-in-savepoint ()

      (define (->register log-id index-of name version)

	(assert (eqv? #f index-of)
		(conc "register-store-indexes: We asked the database for Regisers that aren't an index of anything. We got an index of " index-of " with log-id " log-id " and name " name " at version " version))

	`(,name ,(create-register log-id version)))

      (let ((registers (run-query (db-ctx) select-registers ->register)))
	registers))))

; Allocates a Register in the Backing Store
; Returns an opaque reference that represents the Register allocated.
(define register-store-add!
  (let ((insert-register
	  (make-query
	    "INSERT INTO \"registers\" (\"index-of\", \"name\") VALUES (?1, ?2);"
	    `(,positive-integer-or-false->integer ,require-string)
	    `())))

    (lambda-in-savepoint (index-of name)

      (assert (or (eqv? #f index-of) (integer? index-of))
	      (conc "register-store-add!: index-of argument must be an integer or #f! We got " index-of))

      (assert (string? name)
	      (conc "register-store-add!: name argument must be a string! We got " name))

      (let ((rows-changed (run-exec (db-ctx) insert-register index-of name)))

	(assert (= 1 rows-changed)
		(conc "register-store-add!: Expected 1 row to change when INSERTing register into database. We got " rows-changed))

	(let ((log-id (last-insert-rowid (db-ctx))))
	  (require-integer log-id))))))


; Converts database result sets that describe a number of entries with one row
; per item per entry into entry objects.
;
; start-stream is a procedure of one argument that returns a pair of
; procedures, cleanup and iterator. Each call to iterator produces a row of the
; correct type against the database and calls the procedure supplied in the
; argument to start-stream for each row.
; make-item is a procedure of a variable number of arguments that takes item-id
; and the extra arguments that the query produces and returns an item or
; item-ref suitable for inclusion in an entry.
; The columns produced by the query must be as follows:
; `(log-id entry-number region key ts item-id ...) where ... signifies a number
; of optional columns that will be passed to the procedure specified in the
; make-item argument.
; include-tombstones is a boolean argument that will determine whether entries
; containing no items are returned. This should be #t for everything except for
; record oriented queries.
;
; Returns two values, each a procedure. The first is for cleanup, the second an
; iterator. Calling the iterator will yield two results: the next entry from
; the result set and its entry number. If there were no rows in the database
; result set then the iterator returns #f for both its return values. The
; cleanup procedure must be called when the caller is done with the query
; whether or not they exhaust all the entries in the result set.
; The return values of this procedure must not be passed over a transaction
; boundary so things that call it directly must not use lambda-in-savepoint or
; define-in-transaction and things that receive the resulting procedures must
; be careful in their use of transactions.
; The iterator returns #f when there are no more entries.
(define (wide-entry-item-stream->entry-stream register start-stream make-item include-tombstones)
  ; Each row is passed to ->entry in turn. The rows are flattened entrys so we
  ; receive the entry data for every item in the entry. If the entry has no
  ; items then we should receive a single row for the entry with NULL in the
  ; item fields. Here we maintain a bit of state between each call so that we
  ; know when we've finished receiving all the data about a single entry. This
  ; way, we know when we are able to cons up that entry and start on the next
  ; one.
  (let ((log-id        (register-backing-store-ref register))
	(entry         (make-parameter #f))  ; A place to stash the completed entry if we want to return it to the user.
	(items         (make-parameter '())) ; An accumulator that collects items whilst we wait for the rest before we turn them all into an entry.
	(last-entry-no (make-parameter #f))  ; The entry-number related to the entry in the previous row.
	(last-region   (make-parameter #f))  ; The region related to the entry in the previous row.
	(last-key      (make-parameter #f))  ; The key related to the entry in the previous row. A NULL Key will never be #f: it'll still return #t from key?
	(last-ts       (make-parameter #f))) ; The timestamp related to the entry in the previous row.

    ; Makes the entry and stashes execpt if it's a tombstone and the user
    ; doesn't want to see them.
    (define (make-and-stash-entry! region key ts items)
      (if (or include-tombstones (not (null? items)))
	(entry (apply make-entry region key ts (reverse items)))
	#f))


    ; Stashes an entry and returns its entry-number when it has a whole one and
    ; #f otherwise.
    (define (->entry log-id* entry-number region key ts item-id . item-args)

      (assert (= log-id log-id*)
	      (conc "wide-entry-item-stream->entry-stream: We asked the database for data from log-id " log-id ". We got " log-id*))

      (let ((item (if item-id
		    (apply make-item
			   item-id
			   item-args)
		    #f)))

	(if (not (last-entry-no))
	  (begin
	    ; We're on the first row: initialise stuff
	    (last-entry-no entry-number)
	    (last-region   region)
	    (last-key      key)
	    (last-ts       ts)))

	(if (= (last-entry-no) entry-number) ; Is this another item for the entry in the previous row?
	  (begin
	    ; We're still processing the same entry as before (or we're on the first row).

	    (assert (eqv? (last-region) region)
		    (conc "wide-entry-item-stream->entry-stream: We got different entry regions for different items for entry " entry-number " in log " log-id ". We got " (last-region) " and " region))

	    (assert (key-equal? (last-key) key)
		    (conc "wide-entry-item-stream->entry-stream: We got different entry keys for different items for entry " entry-number " in log " log-id ". We got " (last-key) " and " key))

	    (assert (date=? (last-ts) ts)
		    (conc "wide-entry-item-stream->entry-stream: We got different entry timestamps for different items for entry " entry-number " in log " log-id ". We got " (last-ts) " and " ts))

	    (if item
	      (begin

		(assert (not (null? item))
			(conc "wide-entry-item-stream->entry-stream: We got a null item when we already had some items for key " key ". We already had " (items)))

		(items (cons item (items))))) ; Stash the item

	    'entry-not-complete)
	  (begin
	    ; We've come to the end of the previous entry.

	    (make-and-stash-entry! (last-region) (last-key) (last-ts) (items)) ; Stash the completed entry
	    (items '())                                                        ; Reset items
	    (if item (items (cons item (items))))                              ; Stash the new item
	    (let ((this-entry-no (last-entry-no)))
	      (last-entry-no entry-number)                                     ; Stash the new entry-number
	      (last-region   region)                                           ; Stash the new region
	      (last-key      key)                                              ; Stash the new key
	      (last-ts       ts)                                               ; Stash the new ts

	      this-entry-no)))))


    (receive (process-cleanup process-next-row) (start-stream ->entry)
      (letrec ((cleanup
		 (lambda ()
		   (set! cleanup (lambda () #f))
		   (set! next-row
		     (lambda ()
		       (error "wide-entry-item-stream->entry-stream: next called after cleanup!")))
		   (process-cleanup)))
	       (next-row (lambda () ; The iterator that returns each entry in turn along with its entry-number
			   ; Return entries until there aren't any more then return #f until cleanup is called and then it should return an error.

			   (let loop ((state (process-next-row)))
			     ; Proess next row tries to fetch the next row from the database. If
			     ; there is one it calls ->entry on it and state contains either an
			     ; entry number or 'entry-not-complete. If we've exhausted all the
			     ; rows then state contains '().
			     (case state
			       ('entry-not-complete
				(loop (process-next-row)))
			       ('no-more-rows
				(process-cleanup) ; We're at the end of the result set: clean up the database. ; This is unnecessary (but harmless) as the lower level cleans up by default.
				(set! cleanup  (lambda () #f)) ; The caller might call cleanup but there's nothing left to do.
				(set! next-row (lambda () (values #f #f))) ; The caller hasn't called cleanup yet so just given them #f from now on.
				; After ->entry finishes doing its work for each database row, the last entry is still stashed in the accumulator.
				(let ((this-entry-no (last-entry-no)))
				  (if this-entry-no ; i.e. there were more than zero rows returned from the database.
				    (begin
				      (make-and-stash-entry! (last-region) (last-key) (last-ts) (items))
				      (items '())
				      (last-entry-no #f)
				      (last-region   #f)
				      (last-key      #f)
				      (last-ts       #f)
				      (values (entry) this-entry-no))
				    (values #f #f))))
			       (else
				 (values (entry) state)))))))
	(values
	  (lambda ()
	    (cleanup))
	  (lambda ()
	    (next-row)))))))

; Select entries in the Backing Store by key.
; Performs a range query on the entrys table and returns a pair of procedures.
; One that can be called at the end to clean everything up and one that wraps a
; running query that the caller can call to get the latest entry at the
; specified version number for each key it finds.
; The first time the procedure is called the entry greater than or equal to the
; first key is returned. When there are no more entries, for relevant keys, at
; the version of the register specified in `register`, #f is returned.  When
; the caller has taken enough entries, even if they have reached the end, they
; must call the cleanup procedure.  This procedure returns the equivalent of
; (values cleanup iterator). `cleanup` is first so that the safe thing is
; likely to happen with callers that only expect one return value.
; Tombstones are not visible through this interface. i.e. If the latest entry
; for a particular key has no items then it will not appear at all in the
; result set.
(define entry-store-key-ref

  (let ((select-entry-by-key
	  (make-query
#<<END
	    SELECT
	    "entrys"."log-id"       AS "log-id",
	    "entrys"."entry-number" AS "entry-number",
	    "entrys"."region"       AS "region",
	    "entrys"."key"          AS "key",
	    "entrys"."timestamp"    AS "timestamp",
	    "entry-items"."item-id" AS "item-id",
	    "items"."blob"          AS "blob"

	    FROM
	    (SELECT
	      MAX("entry-number") AS "entry-number",
	      "key"
	      FROM "entrys"
	      WHERE
	      "log-id" = ?1 AND
	      "region" = ?2 AND
	      "entry-number" <= ?3
	      AND "key" BETWEEN ?4 AND ?5
	      GROUP BY "key") AS "specific-entrys"

	    LEFT OUTER JOIN "entrys"
	    ON
	    "specific-entrys"."entry-number" = "entrys"."entry-number"

	    LEFT OUTER JOIN "entry-items"
	    ON
	    "entrys"."log-id" = "entry-items"."log-id" AND
	    "entrys"."entry-number" = "entry-items"."entry-number"

	    LEFT OUTER JOIN "items"
	    ON
	    "items"."item-id" = "entry-items"."item-id"

	    WHERE
	    "entrys"."log-id" = ?1;
END
	    `(,require-integer ,symbol->string    ,require-integer ,key->string ,key->string)                                                           ; (log-id region version key-from key-to)
	    `(,require-integer ,require-integer>0 ,string->symbol ,string->key ,integer->date ,require-integer-or-null ,require-blob-string-or-null)))) ; (log-id entry-number region key timestamp item-id blob)


    (lambda (register region key-a #!optional (key-b key-a)) ; We can't use lambda-in-savepoint with stream-query as it returns a running query out of this lexical scope.

      (assert (eq? #f (autocommit? (db-ctx)))
	      (conc "entry-store-key-ref: Calls into the Backing Store expect to already be inside a transaction but we are not!"))

      (assert (register? register)
	      (conc "entry-store-key-ref: register argument must be a register! We got " register))

      (assert (symbol? region)
	      (conc "entry-store-key-ref: region argument must be a symbol! We got " region))

      (assert (key? key-a)
	      (conc "entry-store-key-ref: key-a argument must be a key! We got " key-a))

      (assert (key? key-b)
	      (conc "entry-store-key-ref: key-b argument must be a key! We got " key-b))

      (wide-entry-item-stream->entry-stream
	register
	(cut stream-query (db-ctx) select-entry-by-key <> (register-backing-store-ref register) region (register-version register) key-a key-b)
	(lambda (item-id blob) ; Put items in the entry's item list.
	  (make-item blob (make-item-ref item-id)))
	#f))))

; Selects the latest entry for every key in the Backing Store.
; This differs from `entry-store-key-ref` because it cannot be scoped to a
; particular range of keys.
; Performs a range query on the entrys table and returns a pair of procedures.
; One that can be called at the end to clean everything up and one that wraps a
; running query that the caller can call to get the latest entry at the
; specified version number for each key it finds.
; The first time the procedure is called the the first key is returned. When
; there are no more entries, for any more keys, at the version of the register
; specified in `register`, #f is returned.  When the caller has taken enough
; entries, even if they have reached the end, they must call the cleanup
; procedure.  This procedure returns the equivalent of (values cleanup
; iterator). `cleanup` is first so that the safe thing is likely to happen with
; callers that only expect one return value.
; Tombstones are not visible through this interface. i.e. If the latest entry
; for a particular key has no items then it will not appear at all in the
; result set.
(define entry-store-keys

  (let ((select-entry-for-keys
	  (make-query
#<<END
	    SELECT
	    "entrys"."log-id"       AS "log-id",
	    "entrys"."entry-number" AS "entry-number",
	    "entrys"."region"       AS "region",
	    "entrys"."key"          AS "key",
	    "entrys"."timestamp"    AS "timestamp",
	    "entry-items"."item-id" AS "item-id",
	    "items"."blob"          AS "blob"

	    FROM
	    (SELECT
	      MAX("entry-number") AS "entry-number",
	      "key"
	      FROM "entrys"
	      WHERE
	      "log-id" = ?1 AND
	      "region" = ?2 AND
	      "entry-number" <= ?3
	      GROUP BY "key") AS "specific-entrys"

	    LEFT OUTER JOIN "entrys"
	    ON
	    "specific-entrys"."entry-number" = "entrys"."entry-number"

	    LEFT OUTER JOIN "entry-items"
	    ON
	    "entrys"."log-id" = "entry-items"."log-id" AND
	    "entrys"."entry-number" = "entry-items"."entry-number"

	    LEFT OUTER JOIN "items"
	    ON
	    "items"."item-id" = "entry-items"."item-id"

	    WHERE
	    "entrys"."log-id" = ?1;
END
	    `(,require-integer ,symbol->string    ,require-integer)                                                                                     ; (log-id region version)
	    `(,require-integer ,require-integer>0 ,string->symbol ,string->key ,integer->date ,require-integer-or-null ,require-blob-string-or-null)))) ; (log-id entry-number region key timestamp item-id blob)


    (lambda (register region) ; We can't use lambda-in-savepoint with stream-query as it returns a running query out of this lexical scope.

      (assert (eq? #f (autocommit? (db-ctx)))
	      (conc "entry-store-keys: Calls into the Backing Store expect to already be inside a transaction but we are not!"))

      (assert (register? register)
	      (conc "entry-store-keys: register argument must be a register! We got " register))

      (assert (symbol? region)
	      (conc "entry-store-keys: region argument must be a symbol! We got " region))

      (wide-entry-item-stream->entry-stream
	register
	(cut stream-query (db-ctx) select-entry-for-keys <> (register-backing-store-ref register) region (register-version register))
	(lambda (item-id blob) ; Put items in the entry's item list.
	  (make-item blob (make-item-ref item-id)))
	#f))))

; Returns a pair of procedures. One that can be called at the end to clean
; everything up and one that wraps a running query that the caller can call to
; get entries and their entry-numbers in order until they've had their fill.
; The first time the procedure is called the entry at the entry number
; specified in `start` is returned. When there are no more entries at the
; version of the register specified in `register`, #f is returned.
; When the caller has taken enough entries, even if they have reached the end,
; they must call the cleanup procedure.
; This procedure returns the equivalent of (values cleanup iterator). `cleanup`
; is first so that the safe thing is likely to happen with callers that only
; expect one return value.
(define entry-store-stream
  (let ((select-entries-in-order
	  (make-query
#<<END
	    SELECT
	    "entrys"."log-id"       AS "log-id",
	    "entrys"."entry-number" AS "entry-number",
	    "entrys"."region"       AS "region",
	    "entrys"."key"          AS "key",
	    "entrys"."timestamp"    AS "timestamp",
	    "entry-items"."item-id" AS "item-id",
	    "items"."blob"          AS "blob"

	    FROM
	    "entrys"

	    LEFT OUTER JOIN "entry-items"
	    ON
	    "entrys"."log-id" = "entry-items"."log-id" AND
	    "entrys"."entry-number" = "entry-items"."entry-number"

	    LEFT OUTER JOIN "items"
	    ON
	    "items"."item-id" = "entry-items"."item-id"

	    WHERE
	    "entrys"."log-id" = ?1
	    AND "entrys"."entry-number" BETWEEN ?3 AND ?2

	    ORDER BY "entrys"."entry-number";
END
            `(,require-integer ,require-integer   ,require-integer)                                                                               ; (log-id version start)
	    `(,require-integer ,require-integer>0 , string->symbol ,string->key ,integer->date ,require-integer-or-null ,require-blob-string-or-null)))) ; (log-id entry-number region key timestamp item-id blob)

    (lambda (register #!optional (start 1)) ; We can't use lambda-in-savepoint with stream-query as it returns a running query out of this lexical scope.

      (assert (eq? #f (autocommit? (db-ctx)))
	      (conc "entry-store-stream: Calls into the Backing Store expect to already be inside a transaction but we are not!"))

      (assert (register? register)
	      (conc "entry-store-stream: register argument must be a register! We got " register))

      (wide-entry-item-stream->entry-stream
	register
	(cut stream-query (db-ctx) select-entries-in-order <> (register-backing-store-ref register) (register-version register) start)
	(lambda (item-id blob) ; Put items in the entry's item list.
	  (make-item blob (make-item-ref item-id)))
	#t))))

; Adds an entry to the log of the specified Register.
; Returns a Register that represents the specified Register with the specified
; entry appended.
(define entry-store-add
  (let ((max-entry-number
	  (make-query
	    "SELECT MAX(\"entry-number\") FROM \"entrys\" WHERE \"log-id\" = ?1;"
	    `(,require-integer)
	    `(,null-or-positive-integer->integer)))
	(insert-entry
	  (make-query
	    "INSERT INTO \"entrys\" (\"log-id\", \"entry-number\", \"region\", \"key\", \"timestamp\") VALUES (?1, ?2, ?3, ?4, ?5);"
	    `(,require-integer ,require-integer ,symbol->string ,key->string ,date->integer)
	    `()))
	(insert-entry-items
	  (make-query
	    "INSERT INTO \"entry-items\" (\"log-id\", \"entry-number\", \"item-id\") VALUES (?1, ?2, ?3);"
	    `(,require-integer ,require-integer ,require-integer)
	    '())))

    (lambda-in-savepoint (register entry)

      (let* ((log-id       (register-backing-store-ref register))
	     (version      (register-version           register))
	     (max-version  (<=1-result (run-query (db-ctx) max-entry-number identity log-id)))
	     (entry-number (add1 max-version)))

	(assert (= max-version version)
		(conc "entry-store-add: We can only add entrys to the latest version of a Register! We got " version " but " register " could be at " max-version))

	; Add the entry to the entrys table.
	(let ((rows-changed (run-exec (db-ctx) insert-entry log-id entry-number (entry-region entry) (entry-key entry) (entry-ts entry))))

	 (assert (= 1 rows-changed)
	  (conc "entry-store-add: Expected 1 row to change when INSERTing entry into database. We got " rows-changed)))

	; Add the entry-items to the entry-items table.
	(for-each
	 (lambda (item-ref)

	   (assert (item-ref? item-ref)
		   (conc "entry-store-add: All entry-items must be item-refs! We got " (entry-items entry)))


	   (let ((rows-changed (run-exec (db-ctx) insert-entry-items log-id entry-number (item-ref-item-id item-ref))))

	    (assert (= 1 rows-changed)
	     (conc "entry-store-add: Expected 1 row to change when INSERTing entry-items into database. We got " rows-changed))

	    item-ref))
	 (entry-items entry))

	(update-register
	 register
	 backing-store-ref: log-id
	 version:           entry-number)))))
)

