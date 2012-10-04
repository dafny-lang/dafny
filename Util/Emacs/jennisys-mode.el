;; jennisys-mode.el - GNU Emacs mode for Jennisys
;; Adapted by Rustan Leino from Jean-Christophe FILLIATRE's GNU Emancs mode for Why

(defvar jennisys-mode-hook nil)

(defvar jennisys-mode-map nil
  "Keymap for Jennisys major mode")

(if jennisys-mode-map nil
  (setq jennisys-mode-map (make-keymap))
  (define-key jennisys-mode-map "\C-c\C-c" 'jennisys-run-boogie)
  (define-key jennisys-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.jen" . jennisys-mode))
       auto-mode-alist))

;; font-lock

(defun jennisys-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst jennisys-font-lock-keywords-1
  (list
   ; comments have the form /* ... */
   '("/\\*\\([^*]\\|\\*[^/]\\)*\\*/" . font-lock-comment-face)
   ; or // ...
   '("//\\([^
]\\)*" . font-lock-comment-face)

   `(,(jennisys-regexp-opt '(
        "interface" "datamodel" "code"
        "var" "constructor" "method"
        "frame" "invariant" "returns" "requires" "ensures"
        )) . font-lock-builtin-face)
   `(,(jennisys-regexp-opt '(
        "if" "then" "else"
        "forall" "exists"
        "this" "in"
        "false" "true" "null")) . font-lock-keyword-face)
   `(,(jennisys-regexp-opt '("array" "bool" "int" "set" "seq")) . font-lock-type-face)
   )
  "Minimal highlighting for Jennisys mode")

(defvar jennisys-font-lock-keywords jennisys-font-lock-keywords-1
  "Default highlighting for Jennisys mode")

;; syntax

(defvar jennisys-mode-syntax-table nil
  "Syntax table for jennisys-mode")

(defun jennisys-create-syntax-table ()
  (if jennisys-mode-syntax-table
      ()
    (setq jennisys-mode-syntax-table (make-syntax-table))
    (set-syntax-table jennisys-mode-syntax-table)
    (modify-syntax-entry ?' "w" jennisys-mode-syntax-table)
    (modify-syntax-entry ?_ "w" jennisys-mode-syntax-table)))

;; menu

(require 'easymenu)

(defun jennisys-menu ()
  (easy-menu-define
   jennisys-mode-menu (list jennisys-mode-map)
   "Jennisys Mode Menu." 
   '("Jennisys"
     ["Run Boogie" jennisys-run-boogie t]
     "---"
     ["Recolor buffer" font-lock-fontify-buffer t]
     "---"
     ))
  (easy-menu-add jennisys-mode-menu))

;; commands

(defun jennisys-command-line (file)
  (concat "boogie " file))

(defun jennisys-run-boogie ()
  "run Boogie to check the Jennisys program"
  (interactive)
  (let ((f (buffer-name)))
    (compile (jennisys-command-line f))))

;; setting the mode

(defun jennisys-mode ()
  "Major mode for editing Jennisys programs.

\\{jennisys-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (jennisys-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(jennisys-font-lock-keywords))
  ; indentation
  ; (make-local-variable 'indent-line-function)
  ; (setq indent-line-function 'jennisys-indent-line)
  ; menu
  ; providing the mode
  (setq major-mode 'jennisys-mode)
  (setq mode-name "Jennisys")
  (use-local-map jennisys-mode-map)
  (font-lock-mode 1)
  (jennisys-menu)
  (run-hooks 'jennisys-mode-hook))

(provide 'jennisys-mode)
