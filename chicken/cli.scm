(use orc orc-rsf)
(use matchable)
(use string-utils)
(use args)
(use srfi-19)
(use files)

; Always create dates in UTC
(local-timezone-locale (utc-timezone-locale))

(define (make-backing-store filename)
  (let ((db (open-backing-store filename)))
    (with-backing-store db initialise-backing-store)
    (when (not (equal? filename 'memory))
      (fprintf (current-error-port) "Created new orc backing store at ~A\n" filename))
    db))

(define (get-backing-store filename)
  (if (file-exists? filename)
    (open-backing-store filename)
    (make-backing-store filename)))

(define (check-not-register name)
  (let ((register (open-register name)))
    (when register
      (fprintf (current-error-port) "Already a Register with the name ~A!\n" name))
    (not register)))

(define formats `(
))

(define get-format (cut assoc <> formats))
(define format-name first)
(define entry-formatter second)
(define diff-formatter  third)
(define format-description fourth)

(define commands '(
))

(define (column-widths get-columns)
  (map
    (compose add1 (cut apply max <>))
    (map
      (cut map string-length <>)
      (call-with-values get-columns list))))

(define commands-column-widths (column-widths (cut unzip3 commands)))

(define (usage)
  (with-output-to-port (current-error-port) (lambda ()
    (print "Usage: " (car (argv)) " [OPTIONS...] COMMAND [ARGS...]")
    (newline)
    (args:width 26)
    (print (args:usage opts))
    (newline)
    (print "Commands:")
    (for-each (lambda (command)
        (for-each display (map string-pad-right command commands-column-widths))
        (newline))
      commands)
    )))


(define backing-store (make-parameter "./orc.register-store"))

(define opts
  (list (args:make-option (S store) (#:required "BACKING-STORE") (conc "Read and write to BACKING-STORE instead of " (backing-store) ".")
          (backing-store arg))
        (args:make-option (? h help) #:none "Print help and exit."
          (usage)
          (exit 1))))

(receive (options args) (args:parse (command-line-arguments) opts)
  (with-backing-store (get-backing-store (backing-store)) (lambda ()
    (match args
      (_ (usage))))))
