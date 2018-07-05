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
	 )


(import chicken scheme)

; Units - http://api.call-cc.org/doc/chicken/language
(use extras data-structures srfi-1 ports)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use srfi-19 merkle-tree message-digest sha2)
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
(define (make-register db-pool #!optional name)
  (let* ((id-log    (create-sqlite-backing-store db-pool #f name: (conc name "-log")        digest-algorithm: 'sha-256))
	 (log       (open-sqlite-backing-store db-pool id-log 0))
	 (id-system (create-sqlite-backing-store db-pool #t name: (conc name "-map-user")   digest-algorithm: 'sha-256 levels: 256))
	 (system    (open-sqlite-backing-store db-pool id-system 0))
	 (id-user   (create-sqlite-backing-store db-pool #t name: (conc name "-map-system") digest-algorithm: 'sha-256 levels: 256))
	 (user      (open-sqlite-backing-store db-pool id-user 0)))

    (create-register
      `(,id-log ,id-system ,id-user)
      (make-merkle-tree sha256-primitive log)
      '() ; FIXME: use merkle-tree not alist! ;(make-merkle-tree sha256-primitive system)
      '() ; FIXME: use merkle-tree not alist! ;(make-merkle-tree sha256-primitive user)
      )))

(define (create-register ids log map-system map-user)

  (assert (list? ids)
	  (conc "create-register: ids argument must be a list! We got " ids))

  (assert (every integer? ids)
	  (conc "create-register: each id in ids argument must be an integer! We got " ids))

  (assert (merkle-tree? log)
	  (conc "create-register: log argument must be a merkle-tree! We got " log))

  `(register ,ids ,log ,map-system ,map-user))

(define (update-register register
			 #!key
			 (ids        (register-ids        register))
			 (log        (register-log        register))
			 (map-system (register-map-system register))
			 (map-user   (register-map-user   register)))
  (create-register ids log map-system map-user))

(define (register? obj)
  (and
    (list? obj)
    (= 5 (length obj))
    (eqv? 'register (car obj))))

(define (register-ids register)
  (assert (register? register)
	  (conc "register-id: register argument must be a register! We got " register))
  (second register))

(define (register-log register)
  (assert (register? register)
	  (conc "register-log: register argument must be a register! We got " register))
  (third register))

(define (register-map-system register)
  (assert (register? register)
	  (conc "register-map-system: register argument must be a register! We got " register))
  (fourth register))

(define (register-map-user register)
  (assert (register? register)
	  (conc "register-map-user: register argument must be a register! We got " register))
  (fifth register))


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


  (let* ((item-ref      (item-item-ref item))
	 (existing-item (current-items-ref item-ref)))

    (if existing-item
      (cond
	((item? existing-item)
	 ; Items need to be equal? rather than eqv? because we don't currently know how to merge references of different types in the item structure.
	 (assert (item-equal? item existing-item)
		 (conc "register-add-item: Found an equivalent item in current items but items do not match! item: " item " , existing-item: " existing-item))
	 register)
	((item-ref? existing-item)
	 (current-items-update! item)
	 register)
	(else
	  (assert #f
		  (conc "register-add-item: Whilst looking for " item ", we found an unexpected item in current-items: " existing-item))))
      (begin
	(current-items-update! item)
	register))))

; An entry serialises to json like this:
; {"index-entry-number":"1","entry-number":"1","entry-timestamp":"2016-04-05T13:23:05Z","key":"SU","item-hash":["sha-256:e94c4a9ab00d951dadde848ee2c9fe51628b22ff2e0a88bff4cca6e4e6086d7a"]}
(define (register-append-entry register entry)

  (assert (register? register)
	  (conc "register-append-entry: register argument must be a register! We got " register))

  (assert (entry? entry)
	  (conc "register-append-entry: entry argument must be an entry! We got " entry))


  (let ((log (register-log register))
	(map (region->map (entry-region entry) register)))

    (assert map
	    (conc "register-append-entry: unexpected region in entry " entry))

    (for-each
      (lambda (item)
	(let ((item-ref (cond
			  ((item-ref? item) item)
			  ((item?     item) (item-item-ref item))
			  (else
			    (assert #f
				    (conc "register-append-entry: Got unknown item-or-ref " item " in item-list for entry " entry))))))

	  ; TODO: add item if it's not found and is an item rather than an item-ref??
	  ; Ensure that the referenced item is in the item stash!
	  (assert (current-items-ref item-ref)
		  (conc "register-append-entry: Got a reference to an unknown item " item " whilst processing " entry))))
      (entry-items entry))

    ; TODO: ensure that we write all the items as refs, not as full items!
    (let ((new-log (merkle-tree-update (merkle-tree-size log) (with-output-to-string (cut write entry)) log))
	  ;(new-map (merkle-tree-update <hash-of-key>          (with-output-to-string (cut write <get-the-item-itself>)) map))
	  (new-map (if (= 0 (length (entry-items entry)))
		     (alist-delete (entry-key entry)       map key-equal?) ; Remove tombstones from the record set
		     (alist-update (entry-key entry) entry map key-equal?))))
      (update-register
	register
	log: new-log
	(case (entry-region entry)
	       ((system) map-system:)
	       ((user)   map-user:))
	new-map))))

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
; This is an alist mapping item-refs to items.
(define current-items
  '())

(define (current-items-ref item-ref)
  (alist-ref item-ref current-items item-ref-equal? #f))

(define (current-items-update! item)
  (set! current-items
    (alist-update (item-item-ref item) item current-items item-ref-equal?)))

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
	 (current-items-ref item-or-ref))
	(else
	  (assert #f
		  (conc "resolve-items: unexpected item-ish " item-or-ref)))))
    lst))



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
			   (string->date timestamp "~Y-~m-~dT~H:~M:~SZ")
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
(define (read-rsf #!optional db-pool name register)

  (assert (or (eq? #f register) (register? register))
	  (conc "read-rsf: register argument must be a register! We got " register))

  (let loop
    ((register (or register (make-register db-pool name)))
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
	  (add1 line-no))))))

)

