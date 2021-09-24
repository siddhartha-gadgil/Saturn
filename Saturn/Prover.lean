class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 

-- Product as an example
instance {α β : Type} [pr : Prover α] [pr' : Prover β] : Prover (α × β) :=
  ⟨fun x => pr.statement x.fst ∧ pr'.statement x.snd, 
    fun x => And.intro (getProof x.fst) (getProof x.snd)⟩

-- Coproduct as an example; observe that the proposition chooses a side
instance {α β : Type} [pr : Prover α] [pr' : Prover β] : Prover (Sum α  β) :=
  ⟨fun x => match x with
    | Sum.inl x => pr.statement x
    | Sum.inr x => pr'.statement x,
    fun x => match x with
      | Sum.inl x => getProof x
      | Sum.inr x => getProof x
    ⟩
