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

(define (write-tsv-oneline entry #!optional prefix)
  (when prefix (printf "~A\t" prefix))
  (printf
      "~A\t~A\t~A\t~A\n"
      (entry-region entry)
      (key->string (entry-key entry))  ; TODO: escape tabs
      (date->string (entry-ts entry) "~Y-~m-~dT~H:~M:~SZ")
      (string-join (map item-blob (entry-items entry)) "\t")))

(define (write-tsv entry #!optional prefix)
  (let ((region (entry-region entry))
        (key    (key->string (entry-key entry)))
        (date   (date->string (entry-ts entry) "~Y-~m-~dT~H:~M:~SZ")))
    (for-each (lambda (entry-item)
      (when prefix (printf "~A\t" prefix))
      (printf "~A\t~A\t~A\t~A\n" region key date (item-blob entry-item)))
      (entry-items entry))))

(define (write-diff entry-formatter old-entry new-entry)
  (when old-entry
    (entry-formatter old-entry "-"))
  (when new-entry
    (entry-formatter new-entry "+")))

(define formats `(
  ("tsv" ,write-tsv ,(cut write-diff write-tsv <> <>)
    "Tab-seperated region, key, timestamp and item blob, one line per entry item (default).")
  ("oneline" ,write-tsv-oneline ,(cut write-diff write-tsv-oneline <> <>)
    "Tab-seperated region, key, timestamp and item blobs, with all items on one line.")
))

(define get-format (cut assoc <> formats))
(define format-name first)
(define entry-formatter second)
(define diff-formatter  third)
(define format-description fourth)

(define commands '(
  ("clone" "<LOCATION> <LABEL>" "Read RSF and store a Register (from STDIN if '-' or file).")
))

(define (column-widths get-columns)
  (map
    (compose add1 (cut apply max <>))
    (map
      (cut map string-length <>)
      (call-with-values get-columns list))))

(define commands-column-widths (column-widths (cut unzip3 commands)))
(define formats-column-widths (column-widths (cut values (map format-name formats) (map format-description formats))))

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
    (newline)
    (print "Formats:")
    (for-each (lambda (format)
        (display (string-pad-right (format-name format) (first formats-column-widths)))
        (display (string-pad-right (format-description format) (second formats-column-widths)))
        (newline))
      formats)
    )))


(define backing-store (make-parameter "./orc.register-store"))
(define current-format (make-parameter (get-format "tsv")))

(define opts
  (list (args:make-option (S store) (#:required "BACKING-STORE") (conc "Read and write to BACKING-STORE instead of " (backing-store) ".")
          (backing-store arg))
        (args:make-option (f format) (#:required "FORMAT") "Use the specified FORMAT for entry output."
          (current-format (get-format arg)))
        (args:make-option (? h help) #:none "Print help and exit."
          (usage)
          (exit 1))))

(receive (options args) (args:parse (command-line-arguments) opts)
  (with-backing-store (get-backing-store (backing-store)) (lambda ()
    (match args
      (("clone" "-" name)
        (when (check-not-register name)
          (with-input-from-port (current-input-port) (cut read-rsf name))))

      (("clone" location name)
        (when (check-not-register name)
          (with-input-from-file location (cut read-rsf name))))

      (_ (usage))))))
