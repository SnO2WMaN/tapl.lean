namespace arith
  inductive term : Type
  | TmTrue : term
  | TmFalse : term
  | TmZero : term
  | TmSucc : term → term
  | TmPred : term → term
  | TmIsZero : term → term
  | TmIf : term → term → term → term 

  namespace term
    private def repr : term → string
    | TmTrue := "true"
    | TmFalse := "false"
    | TmZero := "0"
    | (TmSucc t) := "(succ " ++ (repr t) ++ ")"
    | (TmPred t) := "(pred " ++ (repr t) ++ ")"
    | (TmIsZero t) := "(iszero " ++ (repr t) ++ ")"
    | (TmIf t₁ t₂ t₃) := 
      "(" ++
      "if " ++ (repr t₁) ++ 
      "then " ++ (repr t₂) ++ 
      "else "++ (repr t₃) ++ 
      ")"
    instance : has_repr term := ⟨ repr ⟩  

    def size : term → ℕ
    | (TmSucc t₁) := (size t₁) + 1
    | (TmPred t₁) := (size t₁) + 1
    | (TmIsZero t₁) := (size t₁) + 1
    | (TmIf t₁ t₂ t₃) := (size t₁ + size t₂ + size t₃) + 1
    | _ := 1
     
    theorem term_size_pos : ∀(t : term), 0 < t.size
    | TmZero := nat.succ_pos 0
    | TmTrue := nat.succ_pos 0
    | TmFalse := nat.succ_pos 0
    | (TmPred t₁) := nat.succ_pos (t₁.size)
    | (TmSucc t₁) := nat.succ_pos (t₁.size)
    | (TmIsZero t₁) := nat.succ_pos (t₁.size)
    | (TmIf t₁ t₂ t₃) := nat.succ_pos (t₁.size + t₂.size + t₃.size)

    -- 数値
    def is_numeric_value : term → bool
    | (TmZero) := true
    | (TmSucc t) := is_numeric_value t
    | _ := false

    #eval TmTrue.is_numeric_value  
    #eval (TmSucc TmZero).is_numeric_value  
    #eval (TmSucc TmTrue).is_numeric_value
    #eval (TmSucc (TmSucc TmZero)).is_numeric_value

    -- 値
    def is_value : term → bool
    | (TmTrue) := true
    | (TmFalse) := true
    | (t) := is_numeric_value t

    #eval TmTrue.is_value
    #eval TmFalse.is_value
    #eval TmZero.is_value
    #eval (TmSucc (TmZero)).is_value 

    def eval_term : ∀ (t : term), option (term)
    | (TmIf TmTrue t₂ t₃) := t₂
    | (TmIf TmFalse t₂ t₃) := t₃
    | (TmIf t₁ t₂ t₃) := do
      e₁ ← eval_term t₁,
      TmIf e₁ t₂ t₃
    | (TmSucc t₁) := do
      e₁ ← eval_term t₁,
      TmSucc e₁
    | (TmPred TmZero) := TmZero
    | (TmPred (TmSucc nv₁)) := 
      match nv₁.is_numeric_value with
      | tt := nv₁
      | ff := none
      end
    | (TmPred t₁) := do
      e₁ ← eval_term t₁,
      TmPred e₁
    | (TmIsZero TmZero) := TmTrue
    | (TmIsZero (TmSucc nv₁)) := 
      match nv₁.is_numeric_value with
      | tt := TmFalse
      | ff := none
      end
    | (TmIsZero t₁) := do
      e₁ ← eval_term t₁,
      TmIsZero e₁
    | _ := none
  end term 
end arith