;; dafny-mode.el - GNU Emacs mode for Dafny
;; Adapted by Rustan Leino from Jean-Christophe FILLIATRE's GNU Emancs mode for Why

(defvar dafny-mode-hook nil)

(defvar dafny-mode-map nil
  "Keymap for Dafny major mode")

(if dafny-mode-map nil
  (setq dafny-mode-map (make-keymap))
  (define-key dafny-mode-map "\C-c\C-c" 'dafny-run-boogie)
  (define-key dafny-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.dfy" . dafny-mode))
       auto-mode-alist))

;; font-lock

(defun dafny-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst dafny-font-lock-keywords-1
  (list
   ; comments have the form /* ... */
   '("/\\*\\([^*]\\|\\*[^/]\\)*\\*/" . font-lock-comment-face)
   ; or // ...
   '("//\\([^
]\\)*" . font-lock-comment-face)

   `(,(dafny-regexp-opt '(
        "class" "datatype" "function" "ghost" "var" "method" "constructor" "unlimited"
        "module" "imports" "static" "refines" "replaces" "by"
        "returns" "requires" "ensures" "modifies" "reads" "free"
        "invariant" "decreases"
        )) . font-lock-builtin-face)
   `(,(dafny-regexp-opt '(
        "assert" "assume" "break" "choose" "then" "else" "havoc" "if" "label" "return" "while" "print"
        "old" "forall" "exists" "new" "foreach" "in" "this" "fresh" "allocated"
        "match" "case" "false" "true" "null")) . font-lock-keyword-face)
   `(,(dafny-regexp-opt '("array" "array2" "array3" "bool" "nat" "int" "object" "set" "seq")) . font-lock-type-face)
   )
  "Minimal highlighting for Dafny mode")

(defvar dafny-font-lock-keywords dafny-font-lock-keywords-1
  "Default highlighting for Dafny mode")

;; syntax

(defvar dafny-mode-syntax-table nil
  "Syntax table for dafny-mode")

(defun dafny-create-syntax-table ()
  (if dafny-mode-syntax-table
      ()
    (setq dafny-mode-syntax-table (make-syntax-table))
    (set-syntax-table dafny-mode-syntax-table)
    (modify-syntax-entry ?' "w" dafny-mode-syntax-table)
    (modify-syntax-entry ?_ "w" dafny-mode-syntax-table)))

;; menu

(require 'easymenu)

(defun dafny-menu ()
  (easy-menu-define
   dafny-mode-menu (list dafny-mode-map)
   "Dafny Mode Menu." 
   '("Dafny"
     ["Run Boogie" dafny-run-boogie t]
     "---"
     ["Recolor buffer" font-lock-fontify-buffer t]
     "---"
     ))
  (easy-menu-add dafny-mode-menu))

;; commands

(defun dafny-command-line (file)
  (concat "boogie " file))

(defun dafny-run-boogie ()
  "run Boogie to check the Dafny program"
  (interactive)
  (let ((f (buffer-name)))
    (compile (dafny-command-line f))))

;; setting the mode

(defun dafny-mode ()
  "Major mode for editing Dafny programs.

\\{dafny-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (dafny-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(dafny-font-lock-keywords))
  ; indentation
  ; (make-local-variable 'indent-line-function)
  ; (setq indent-line-function 'dafny-indent-line)
  ; menu
  ; providing the mode
  (setq major-mode 'dafny-mode)
  (setq mode-name "Dafny")
  (use-local-map dafny-mode-map)
  (font-lock-mode 1)
  (dafny-menu)
  (run-hooks 'dafny-mode-hook))

(provide 'dafny-mode)
