;;; civl-syntax.el --- CIVL-C Syntax Highlighting

;;;###autoload
(defun civl-syntax-init ()
  "CIVL-C syntax highlighting"
  (define-derived-mode civl-mode c-mode
    (setq mode-name "CIVL-C"))
  (add-hook 'civl-mode-hook'
    (lambda ()
      (font-lock-add-keywords nil
       '(("\\<_Bool\\>" . font-lock-type-face)
	 ("\\$\\(bundle\\|scope\\|proc\\|message\\|gcomm\\|comm\\)\\>" . font-lock-type-face)
	 ("\\$\\(here\\|root\\|self\\|true\\|false\\|proc_null\\)\\>" . font-lock-constant-face)
	 ("\\$\\(scope_parent\\|scopeof\\|choose_int\\|wait\\|exit\\|message_pack\\|message_tag\\|message_dest\\|message_size\\|message_unpack\\|gcomm_create\\|comm_create\\|comm_size\\|comm_place\\|comm_enqueue\\|comm_probe\\|comm_seek\\|comm_dequeue\\|assert\\|malloc\\|free\\|comm_destroy\\|gcomm_destroy\\|proc_defined\\|scope_defined\\|gcomm_defined\\|comm_defined\\|waitall\\)\\>" . font-lock-builtin-face)
	 ("\\$\\(when\\|choose\\|spawn\\|atom\\|atomic\\|input\\|output\\|assume\\|forall\\|exists\\|requires\\|ensures\\|invariant\\|collective\\)\\>" . font-lock-keyword-face)))))
  
  (add-to-list 'auto-mode-alist '("\\.\\(cvl\\|cvh\\)" . civl-mode)))

(defalias 'civl-syntax #'civl-syntax-init)
(provide 'civl-syntax)
