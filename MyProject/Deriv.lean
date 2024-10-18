import MyProject.Limit

-- 微分係数の定義
def HasDerivAt (f : Real → Real) (f' a : Real) : Prop :=
  IsLimAt (fun h ↦ (f (a + h) - f a) / h) f' 0

def deriv (f : Real → Real) (a : Real) {f' : Real} (h : HasDerivAt f f' a): Real := f'
