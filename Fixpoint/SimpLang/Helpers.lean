def myFold (fn : γ → α → γ) (agg : γ) (as : List α) : γ :=
  match as with
  | [] => agg
  | a::as => myFold fn (fn agg a) as

def shcFold (fn : γ → α → γ) (agg : γ) (til : γ → α → Bool) (as : List α) : γ :=
  match as with
  | [] => agg
  | a::as => if til agg a then agg else shcFold fn (fn agg a) til as

def contains_duplicates {α} [BEq α] (as : List α) : Bool :=
  let x := shcFold
    (λg => (·::g))
    []
    (λg => g.contains)
    as
  match x with
  | [] => False
  | _ => True
