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
;;;  Copyright (C) 2018, Andy Bennett, Register Dynamics Limited.
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
	 register?
	 register-root-digest
	 register-add-item
	 register-append-entry
	 register-records
	 register-record-ref

	 ; constructor
	 ; predicates
	 ; accessors
	 ; operations

	 make-key
	 key?
	 key-equal?
	 make-entry
	 entry?
	 entry-region
	 entry-key
	 entry-ts
	 entry-items
	 make-item
	 item?
	 make-item-ref
	 item-ref?
	 item-eqv?
	 item-equal?
	 item-item-ref
	 item-blob
	 item-ref?
	 item-or-ref?
	 item-ref-equal?
	 item-ref-type
	 item-ref-algo
	 item-ref-digest

	 ; RSF
	 read-rsf

	 ; Backing Stores
	 initialise-backing-store
	 )


(import chicken scheme)

; Units - http://api.call-cc.org/doc/chicken/language
(use extras data-structures srfi-1 ports)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use srfi-19 merkle-tree message-digest sha2 sql-de-lite)
;(use numbers) ; The Sparse Merkle Tree needs some *really* big numbers!



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
(define (make-register #!optional name)

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
(define (make-item blob #!optional (ref (blob->item-ref blob)))

  (assert (or (string? blob)
	      (blob? blob))
	  (conc "make-item: blob argument must be a string or blob! We got " blob))

  `(item ,ref ,blob))

(define (item? obj)
  (and
    (list? obj)
    (= 3 (length obj))
    (eqv? 'item (car obj))))

(define (item-item-ref item)
  (assert (item? item)
	  (conc "item-item-ref: entry argument must be an entry! We got " item))
  (second item))

(define (item-blob item)
  (assert (item? item)
	  (conc "item-blob: entry argument must be an entry! We got " item))
  (third item))


;; item-ref

; A reference to an item.
; The reference can be in terms of a digest or a backing store and some key
; data.
; For now we only support reference by digest.
(define (make-item-ref algo digest)

  (assert (eqv? 'sha-256 algo)
	  (conc "make-item-ref: Only 'sha-256 item digest algorithms are supported! We got " algo))

  (assert (blob? digest)
	  (conc "make-item-ref: digest argument must be a blob! We got " digest))

  `(item-ref digest (,algo ,digest)))

; Makes an item-ref that points to the item directly in the Backing Store.
; This constructor should only be called by the Backing Store code.
(define (make-item-ref-opaque item-id)

  (assert (integer? item-id)
	  (conc "make-item-ref-opaque: item-id argument must be an integer! We got " item-id))

  `(item-ref opaque (,item-id)))

(define (item-ref? obj)
  (and
    (list? obj)
    (= 3 (length obj))
    (eqv? 'item-ref (car obj))))

(define (item-or-ref? obj)
  (or (item?     obj)
      (item-ref? obj)))

(define (item-ref-type item-ref)

  (assert (item-ref? item-ref)
	  (conc "item-ref-type: item-ref argument must be an item-ref! We got " item-ref))

  (second item-ref))

(define (item-ref-algo item-ref)

  (assert (item-ref? item-ref)
	  (conc "item-ref-algo: item-ref argument must be an item-ref! We got " item-ref))

  (assert (eqv? 'digest (item-ref-type item-ref))
	  (conc "item-ref-algo: item-ref argument must be a 'digest item-ref! We got " item-ref))

  (first (third item-ref)))

(define (item-ref-digest item-ref)

  (assert (item-ref? item-ref)
	  (conc "item-ref-digest: item-ref argument must be an item-ref! We got " item-ref))

  (assert (eqv? 'digest (item-ref-type item-ref))
	  (conc "item-ref-digest: item-ref argument must be a 'digest item-ref! We got " item-ref))

  (second (third item-ref)))

(define (item-ref-item-id item-ref)

  (assert (item-ref? item-ref)
	  (conc "item-ref-item-id: item-ref argument must be an item-ref! We got " item-ref))

  (assert (eqv? 'opaque (item-ref-type item-ref))
	  (conc "item-ref-item-id: item-ref argument must be an 'opaque item-ref! We got " item-ref))

  (first (third item-ref)))


;; Operations

;; Operations on Environments

(define current-environment
  (make-parameter (make-environment) environment?))


;; Operations on Registers

(define (region->map region register)
  (case region
    ((system) (register-map-system register))
    ((user)   (register-map-user   register))
    (else     #f)))

(define (register-root-digest register)

  (assert (register? register)
	  (conc "register-root-digest: register argument must be a register! We got " register))

  (let ((log (register-log register)))
    (merkle-tree-hash log)))


; Adds the specified item to the item pool.
; This procedure adds full items. item-refs are not allowed. For that you need register-declare-item.
(define (register-add-item register item)

  (assert (register? register)
	  (conc "register-add-item: register argument must be a register. We got " register))


  (assert (item? item)
	  (conc "register-add-item: item argument must be an item. We got " item))


  (let* ((item-ref      (item-item-ref  item))
	 (existing-item (item-store-ref item-ref)))

    (if existing-item
      (cond
	((item? existing-item)
	 ; Items need to be equal? rather than eqv? because we don't currently know how to merge references of different types in the item structure.
	 (assert (item-eqv? item existing-item)
		 (conc "register-add-item: Found an equivalent item in current items but items do not match! item: " item " , existing-item: " existing-item))
	 (current-items-update! item (item-item-ref existing-item)) ; Make it available in the current scope.
	 register)
	((item-ref? existing-item)
	 (let ((item-store-ref (item-store-add! item))) ; Add it to the Backing Store.
	   (current-items-update! item item-store-ref) ; Make it available in the current scope.
	   register))
	(else
	  (assert #f
		  (conc "register-add-item: Whilst looking for " item ", we found an unexpected item in current-items: " existing-item))))
      (begin
	(let ((item-store-ref (item-store-add! item))) ; Add it to the Backing Store.
	  (current-items-update! item item-store-ref) ; Make it available in the current scope.
	  register)))))

; An entry serialises to json like this:
; {"index-entry-number":"1","entry-number":"1","entry-timestamp":"2016-04-05T13:23:05Z","key":"SU","item-hash":["sha-256:e94c4a9ab00d951dadde848ee2c9fe51628b22ff2e0a88bff4cca6e4e6086d7a"]}
(define (register-append-entry register entry)

  (assert (register? register)
	  (conc "register-append-entry: register argument must be a register! We got " register))

  (assert (entry? entry)
	  (conc "register-append-entry: entry argument must be an entry! We got " entry))

  ; Returns an opaque item-ref or #f if the supplied item-ref was of type
  ; 'digest and not found the current scope.
  (define (item-ref->opaque obj)
    (case (item-ref-type obj)
      ((digest)
       ; TODO: add obj if it's not found and is an item rather than an item-ref??
       (current-items-ref obj))
      ((opaque) obj)
      (else
	(assert #f
		(conc "reigster-append-entry: Got an item-ref of unknown type! We got " obj)))))

  ; prepare the entry by ensuring that we have opaque item-refs in the item list
  ; pass it to entry-store add
  ; return the register that entry-store-add gives us
  (entry-store-add
    register
    (update-entry
      entry
      items: (map (lambda (obj)
		    (let ((item-ref (item-ref->opaque
				      (cond
					((item-ref? obj) obj)
					((item?     obj) (item-item-ref obj))
					(else
					  (assert #f
						  (conc "register-append-entry: Got unknown item-or-ref " obj " in item-list for entry " entry)))))))

		      (assert item-ref ; This happens when the item isn't passed to register-add-item before appearing in an entry passed to register-append-entry.
			      (conc "register-append-entry: 'digest reference of item " obj " could not be resolved to an item in the current scope. Whilst processing entry " entry))

		      (assert (eqv? 'opaque (item-ref-type item-ref))
			      (conc "register-append-entry: Got a reference to an item that did not resolve to an 'opaque item-ref! We got " obj " that resolved to " item-ref " whilst processing entry " entry))

		      (assert (current-items-ref item-ref) ; This happens when we get an opaque, possibly valid, reference to an item that isn't in the current scope.
			      (conc "register-append-entry: Got a reference to an item " obj " that was not declared in the current scope whilst processing " entry))

		      item-ref))
		  (entry-items entry)))))


; TODO: probably best to rework this as an iterator interface!
; Returns a list of entries.
; We don't expose "records" (key->entry thingies) outside the module.
(define (register-records region register)

  (assert (register? register)
	  (conc "register-records: register argument must be a register. We got " register))

  (let ((the-map (region->map region register)))

    (assert the-map
	    (conc "register-records: unexpected region " region))

    (map
      (lambda (record)
	;(assert (and (list? record) (= 2 (length record)))
	;	(conc "register-records: expected a record in " region " map! We got: " record))

	(let ((key   (car record))
	      (entry (cdr record)))

	  (apply
	    make-entry
	    (entry-region  entry)
	    (entry-key     entry)
	    (entry-ts      entry)
	    (resolve-items (entry-items entry)))))
      the-map)))

; Returns the entry corresponding to the key or #f if there isn't one.
(define (register-record-ref region key register)

  (assert (register? register)
	  (conc "register-records: register argument must be a register. We got " register))

  (assert (key? key)
	  (conc "register-records: key argument must be a key. We got " key))

  (let ((the-map (region->map region register)))

    (assert the-map
	    (conc "register-records: unexpected region " region))

    (let ((entry (alist-ref key the-map key-equal? #f)))
      (if entry
	(apply
	  make-entry
	  (entry-region  entry)
	  (entry-key     entry)
	  (entry-ts      entry)
	  (resolve-items (entry-items entry)))
	#f))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Higher level and compound operations on ADTs

;; Operations on Keys

(define (key-equal? a b)

  (assert (key? a)
	  (conc "key-equal?: a argument must be a key! We got " a))

  (assert (key? b)
	  (conc "key-equal?: b argument must be a key! We got " b))

  (equal? a b))


;; Operations on Entrys


;; Operations on Items

; TODO: make sure this is threadsafe!
; This is an alist of item-refs that we have seen. It maps to and from the
; 'digest form and the 'opaque form. We could use the Backing Store were it not
; for the requirement that we keep track of which items and item-refs we've
; seen in the "current scope".
; We can't currently handle the same item referred to by more than one distinct
; 'digest item-ref.

; This is the list of item-refs seen in the current context. i.e. rsf file.
(define current-items
  (make-parameter '()))

(define (current-items-ref item-ref)
  (alist-ref item-ref (current-items) item-ref-equal?))

(define (current-items-update! item item-store-ref)

  (assert (item? item)
	  (conc "current-item-update!: item argument must be an item! We got " item))

  ; FIXME: Really we require one 'digest and one 'opaque but for now we require
  ;        each one to be in a specific place rather than handling it more
  ;        elegantly. To fix this we'd need to support mapping from one 'opaque
  ;        to one or more 'digests.
  (assert (eqv? 'digest (item-ref-type (item-item-ref item)))
	  (conc "current-item-update!: item argument must contain a 'digest item-ref! We got " item))

  (assert (eqv? 'opaque (item-ref-type item-store-ref))
	  (conc "current-item-update!: item-store-ref argument must contain an 'opaque item-ref! We got " item-store-ref))

  (current-items-update!* (item-item-ref item) item-store-ref)
  (current-items-update!* item-store-ref     (item-item-ref item)))

(define (current-items-update!* item-ref-a item-ref-b)

  (let ((existing (current-items-ref item-ref-a)))
    (if existing
      (begin
	(fprintf (current-error-port) "WARNING: item ~A has already been declared in this scope!\n" item-ref-a)
	(assert (item-ref-equal? existing item-ref-b)
		(conc "current-items-update!*: item ~A has already been defined as " existing " but we're being asked to redefine it as " item-ref-b))
	(current-items))
      (begin
	(current-items
	  (alist-update item-ref-a item-ref-b (current-items) item-ref-equal?))
	(current-items)))))

(define (blob->item-ref blob #!optional (algo 'sha-256))

  (assert (or (string? blob)
	      (blob? blob))
	  (conc "blob->item-ref: blob argument must be a string or blob! We got " blob))

  (assert (eqv? 'sha-256 algo)
	  (conc "blob->item-ref: Only 'sha-256 item digest algorithms are supported! We got " algo))

  (let ((digest ((cond
		   ((string? blob) message-digest-string)
		   ((blob?   blob) message-digest-blob))
		 (sha256-primitive)
		 blob
		 'blob)))

    (make-item-ref algo digest)))

; Compare items.
; They must be equivalent. i.e. they must contain the same blob but the
; reference can be different if it is a different type or algorithm.
; TODO: for now we require references to be equal if they are of the same type.
;       We can relax this for 'digest item-refs provided the algorithms differ.
(define (item-eqv? a b)

  (assert (item? a)
	  (conc "item-equal?: a argument must be an item! We got " a))

  (assert (item? b)
	  (conc "item-equal?: b argument must be an item! We got " b))

  (let ((ref-a (item-item-ref a))
	(ref-b (item-item-ref b)))
    (and
      (equal? (item-blob a) (item-blob b))
      (or (item-ref-equal? ref-a ref-b) ; references are equal
	  (not (eqv? (item-ref-type ref-a) (item-ref-type ref-b))))))) ; references are not equal but they're of different types anyway

; Compare items.
; They must be equal?. i.e. they must contain the same blob and the same
; reference.
; Later we can add support for item-equivalence where the blbs are the same and
; the references are different.
(define (item-equal? a b)

  (assert (item? a)
	  (conc "item-equal?: a argument must be an item! We got " a))

  (assert (item? b)
	  (conc "item-equal?: b argument must be an item! We got " b))

  (equal? a b))

; Compare item-refs.
; They must be equal?. i.e. they must be of the same type, encoded in the same
; algorithm and the digests must match.
(define (item-ref-equal? a b)

  (assert (item-ref? a)
	  (conc "item-ref-equal?: a argument must be an item-ref! We got " a))

  (assert (item-ref? b)
	  (conc "item-ref-equal?: b argument must be an item-ref! We got " b))

  (equal? a b))

; Takes a list of items or item-refs and returns the corresponding list of items.
(define (resolve-items lst)

  (assert (list? lst)
	  (conc "resolve-items: items argument must be a list! We got " lst))

  (map
    (lambda (item-or-ref)
      (cond
	((item? item-or-ref)
	 item-or-ref)
	((item-ref? item-or-ref)
	 ; We could do this dereferencing here or we could do it in the accessor.
	 ; How lazy do we want to be?
	 ; How easy would it be to do given that the accessor actually returns a list of items?
	 ; What if the item-ref returns an item-ref? What if we resolve it and that results in an infinite loop?
	 (item-store-ref item-or-ref))
	(else
	  (assert #f
		  (conc "resolve-items: unexpected item-ish " item-or-ref)))))
    lst))


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
(define (read-rsf #!optional name register)

  (assert (or (eq? #f register) (register? register))
	  (conc "read-rsf: register argument must be a register! We got " register))

  (parameterize ((current-items '()))
    (let loop
      ((register (or register (make-register name)))
       (line     (read-line))
       (line-no  1))

      (assert (register? register)
	      (conc "read-rsf: The handler for line " (sub1 line-no) " returned " register " which is not a register!"))

      (cond
	((eof-object? line) register)
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
	    (read-line)
	    (add1 line-no)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SQLite Backing Store

; Initialises an SQLite Database with the appropriate schema.
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
; Returns #t if the database was successfully initialised and throws an
; exception otherwise.
;
; There is currently no provision for customising the table names or having
; more than one backing store per database file.
(define (initialise-backing-store filename)
  (let ((db (open-database filename)))
    (with-transaction
      db
      (lambda ()
	(for-each
	  (lambda (q)
	    (exec
	      (sql db q)))
	  `("CREATE TABLE \"entry-items\" (\"log-id\"  NOT NULL , \"entry-number\"  NOT NULL , \"item-id\"  NOT NULL );"
	    "CREATE TABLE \"entrys\" (\"log-id\" INTEGER NOT NULL , \"entry-number\" INTEGER NOT NULL , \"region\" TEXT NOT NULL , \"key\" TEXT NOT NULL , \"timestamp\" INTEGER NOT NULL , PRIMARY KEY (\"log-id\", \"entry-number\"));"
	    "CREATE TABLE \"item-digests\" (\"item-id\" INTEGER NOT NULL , \"algorithm\" TEXT NOT NULL , \"digest\" BLOB NOT NULL , PRIMARY KEY (\"item-id\", \"algorithm\"));"
	    "CREATE TABLE \"items\" (\"item-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"blob\" BLOB NOT NULL  UNIQUE );"
	    "CREATE TABLE \"registers\" (\"log-id\" INTEGER PRIMARY KEY  NOT NULL  UNIQUE , \"index-of\" INTEGER NOT NULL , \"name\" TEXT NOT NULL );"
	    "CREATE INDEX \"entry-items-log-id-entry-number-item-id\" ON \"entry-items\" (\"log-id\" ASC, \"entry-number\" ASC, \"item-id\" ASC);"
	    "CREATE UNIQUE INDEX \"entrys-region-key-entry-number-log-id\" ON \"entrys\" ( \"region\" ASC, \"key\" ASC, \"entry-number\" ASC, \"log-id\" ASC);"
	    "CREATE UNIQUE INDEX \"item-digests-algorithm-digest\" ON \"item-digests\" (\"algorithm\" ASC, \"digest\" ASC);"
	    "CREATE UNIQUE INDEX \"registers-index-of-name\" ON \"registers\" (\"index-of\" ASC, \"name\" ASC);"))
	#t))))

(define db-ctx (make-parameter (open-database "orc.backing-store.sqlite")))

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


; Look up an item in the Backing Store by item-ref.
; Returns an item if successful, #f if the item could not be found and throws
; an exception otherwise.
; TODO: Support returning just an item-ref if that's all we've got. We'd need to switch the order of the LEFT JOIN around!
(define item-store-ref

  (let ((select-item-by-digest
	 (make-query
	  "SELECT \"items\".\"item-id\", \"items\".\"blob\" from \"items\" LEFT JOIN \"item-digests\" ON \"items\".\"item-id\" = \"item-digests\".\"item-id\" WHERE \"item-digests\".\"algorithm\" = ?1 AND \"item-digests\".\"digest\" = ?2;"
	 `(,symbol->string  ,require-blob)              ; (algorithm digest)
	 `(,require-integer ,require-blob-or-string)))) ; (item-id   blob)


    (lambda (item-ref)

      (define (->item-ref item-id blob)
	(make-item blob (make-item-ref-opaque item-id)))

      (assert (item-ref? item-ref)
	      (conc "item-store-ref: item-ref argument must be an item-ref! We got " item-ref))

      (case (item-ref-type item-ref)
	((digest)

	 (let ((items (run-query (db-ctx) select-item-by-digest ->item-ref (item-ref-algo item-ref) (item-ref-digest item-ref))))
	   (<=1-result items)))

	(else
	  (assert #f
		  (conc "item-store-ref: unsupported item-ref type! We got " (item-ref-type item-ref))))))))

; Add an item to the Backing Store.
; Returns an item-ref if successful and throws an exception otherwise.
(define item-store-add!
  (let ((insert-item
	  (make-query
	    "INSERT INTO \"items\" (\"blob\") VALUES (?1);"
	    `(,require-blob-or-string) ; blob
	    `())))                     ; nothing

    (lambda (item)

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

	(let* ((ref (item-item-ref item)))
	  (item-store-add-digest! item-id ref) ; FIXME: here or in register-add-item?? The current arrangement assumes that the ref is always of 'digest type.
	  (make-item-ref-opaque item-id))))))


; Add a 'digest item-ref to the Backing Store.
; Returns #t if successful and throws an exception otherwise.
(define item-store-add-digest!
  (let ((insert-item-digest
	  (make-query
	    "INSERT INTO \"item-digests\" (\"item-id\", \"algorithm\", \"digest\") VALUES (?1, ?2, ?3);"
	    `(,require-integer ,symbol->string ,require-blob)
	    `())))

    (lambda (item-id item-ref)

      (assert (integer? item-id)
	      (conc "item-store-add-digest!; item-id argument must be an integer! We got " item-id))

      (assert (item-ref? item-ref)
	      (conc "item-store-add-digest!: item-ref argument must be an item-ref! We got " item-ref))

      (assert (eqv? 'digest (item-ref-type item-ref))
	      (conc "item-store-add-digest!: Only 'digest item-refs are currently supported. We got " item-ref))

      (let ((rows-changed (run-exec (db-ctx) insert-item-digest item-id (item-ref-algo item-ref) (item-ref-digest item-ref))))

	(assert (= 1 rows-changed)
		(conc "item-store-add-digest!: Expected 1 row to change when INSERTing item-ref into database. We got " rows-changed))

	#t))))


; Allocates a Register in the Backing Store
; Returns an opaque reference that represents the Register allocated.
(define register-store-add!
  (let ((insert-register
	  (make-query
	    "INSERT INTO \"registers\" (\"index-of\", \"name\") VALUES (?1, ?2);"
	    `(,positive-integer-or-false->integer ,identity)
	    `())))

    (lambda (index-of name)

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
; query-runner is a procedure of one argument that runs a query that produces
; rows of the correct type against the database and calls the procedure
; supplied in its argument for each row.
; The column produced by the query must be as follows:
; `(log-id entry-number region key ts item-id blob)
(define (wide-entry-item-rows->entries register region query-runner)
  ; Each row is passed to ->entry in turn. The rows are flattened entrys so we
  ; receive the entry data for every item in the entry. If the entry has no
  ; items then we should receive a single row for the entry with NULL in the
  ; item fields. Here we maintain a bit of state between each call so that we
  ; know when we've finished receiving all the data about a single entry. This
  ; way, we know when we are able to cons up that entry and start on the next
  ; one.
  (let ((log-id   (register-backing-store-ref register))
	(entries  (make-parameter '())) ; An accumulator that collects the completed entries.
	(items    (make-parameter '())) ; An accumulator that collects items whilst we wait for the rest before we turn them all into an entry.
	(last-key (make-parameter #f))  ; The key related to the entry in the previous row. A NULL Key will never be #f: it'll still return #t from key?
	(last-ts  (make-parameter #f))) ; The timestamp related to the entry in the previous row.

    ; Makes the entry and stashes it if it is not a tombstone.
    (define (make-and-stash-entry! region key ts items)
      (if (not (null? items))
	(entries (cons (apply make-entry region key ts (reverse items)) (entries)))))


    (define (->entry log-id* entry-number region* key ts item-id blob)

      (assert (= log-id log-id*)
	      (conc "entry-store-ref: We asked the database for data from log-id " log-id ". We got " log-id*))

      (assert (eqv? region region*)
	      (conc "entry-store-ref: We asked the database for data from region " region ". We got " region*))

      (let ((item (if blob
		    (make-item
		      blob
		      (make-item-ref-opaque item-id))
		    #f)))

	(if (not (last-key))
	  (begin
	    ; We're on the first row: initialise stuff
	    (last-key key)
	    (last-ts  ts)))

	(if (key-equal? (last-key) key) ; Is this another item for the entry in the previous row?
	  (begin
	    ; We're still processing the same entry as before (or we're on the first row).

	    (assert (eqv? region region*)
		    (conc "entry-store-ref: We got different entry regions for different items for key " key " in log " log-id ". We got " region " and " region*))

	    (assert (date=? (last-ts) ts)
		    (conc "entry-store-ref: We got different entry timestamps for different items for key " key " in log " log-id ". We got " (last-ts) " and " ts))

	    (if item
	      (begin

		(assert (not (null? item))
			(conc "entry-store-ref: We got a null item when we already had some items for key " key ". We already had " (items)))

		(items (cons item (items)))))) ; Stash the item
	  (begin
	    ; We've come to the end of the previous entry.

	    (assert (eqv? region region*)
		    (conc "entry-store-ref: We got different entry regions for different keys " (last-key) " and " key " in log " log-id ". We got " region " and " region*))

	    (make-and-stash-entry! region (last-key) (last-ts) (items)) ; Stash the completed entry
	    (items '())                                                 ; Reset items
	    (if item (items (cons item (items))))                       ; Stash the new item
	    (last-key key)                                              ; Stash the new key
	    (last-ts  ts))))                                            ; Stash the new ts

      #f)


    (let ((_ (query-runner ->entry)))
      ; After ->entry finishes doing its work for each database row, the last entry is still stashed in the accumulator.
      (make-and-stash-entry! region (last-key) (last-ts) (items))
      (items '())
      (last-key #f)
      (last-ts #f)
      (reverse (entries))))) ; Return the entries in the order we received them from the database (whatever that is).

; Select entries in the Backing Store by key.
; Performs a range query on the entrys table and returns a list of entrys
; containing the latest entry at the specified version number for each key it
; finds.
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
	    `(,require-integer ,symbol->string ,require-integer ,key->string ,key->string)                                                            ; (log-id region version key-from key-to)
	    `(,require-integer ,require-integer ,string->symbol ,string->key ,integer->date ,require-integer-or-null ,require-blob-string-or-null)))) ; (log-id entry-number region key timestamp item-id blob)


    (lambda (register region key-a #!optional (key-b key-a))

      (assert (register? register)
	      (conc "entry-store-key-ref: register argument must be a register! We got " register))

      (assert (symbol? region)
	      (conc "entry-store-ref: region argument must be a symbol! We got " region))

      (assert (key? key-a)
	      (conc "entry-store-ref: key-a argument must be a key! We got " key-a))

      (assert (key? key-b)
	      (conc "entry-store-ref: key-b argument must be a key! We got " key-b))

      (wide-entry-item-rows->entries
	register
	region
	(cut run-query (db-ctx) select-entry-by-key <> (register-backing-store-ref register) region (register-version register) key-a key-b)))))

; Selects the latest entry for every key in the Backing Store.
; Performs a range query on the entrys table and returns a list of entrys
; containing the latest entry at the specified version number for each key it
; finds.
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
	    `(,require-integer ,symbol->string ,require-integer)                                                                                      ; (log-id region version)
	    `(,require-integer ,require-integer ,string->symbol ,string->key ,integer->date ,require-integer-or-null ,require-blob-string-or-null)))) ; (log-id entry-number region key timestamp item-id blob)


    (lambda (register region)

      (assert (register? register)
	      (conc "entry-store-key-ref: register argument must be a register! We got " register))

      (assert (symbol? region)
	      (conc "entry-store-ref: region argument must be a symbol! We got " region))

      (wide-entry-item-rows->entries
	register
	region
	(cut run-query (db-ctx) select-entry-for-keys <> (register-backing-store-ref register) region (register-version register))))))

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

    (lambda (register entry)

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

	   (assert (eqv? 'opaque (item-ref-type item-ref))
		   (conc "entry-store-add: We can only add entrys that use opaque item-refs! We got " (entry-items entry) ))


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

