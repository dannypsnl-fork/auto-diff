module AutoDiff

record Diff a where
    constructor MkDiff
    getGradient : a
    getValue : a

-- dC/dx = 0
export
constant : Num a => a -> Diff a
constant = MkDiff 0

-- dx/dx = 1
export
independent : Num a => a -> Diff a
independent = MkDiff 1

-- du/dx = du/dv * dv/dx
export
elementary : Num a => (a -> a) -> (a -> a) -> Diff a -> Diff a
elementary f f' (MkDiff dy y) = MkDiff (f' y * dy) (f y)

arithmetic : Num a => (a -> a -> a) -> (a -> a -> (a, a)) -> Diff a -> Diff a -> Diff a
arithmetic f f' (MkDiff du u) (MkDiff dv v) =
  let (dx, dy) = f' u v in MkDiff (dx * du + dy * dv) (f u v)

squared : Num a => a -> a
squared x = x * x

diff' : Num a => (Diff a -> Diff a) -> a -> Diff a
diff' f = f . independent
export
diff : Num a => (Diff a -> Diff a) -> a -> a
diff f = getGradient . diff' f

export
sin' : Diff Double -> Diff Double
sin' = elementary sin cos
export
cos' : Diff Double -> Diff Double
cos' = elementary cos (negate . sin)

Eq a => Eq (Diff a) where
  u == v = getValue u == getValue v

Ord a => Ord (Diff a) where
  compare u v = compare (getValue u) (getValue v)

Num a => Num (Diff a) where
  -- d(u+v) = du + dv
  (+) = arithmetic (+) (\_, _ => (1, 1))
  -- d(uv) = v(du) + u(dv)
  (*) = arithmetic (*) (\u, v => (v, u))
  fromInteger = constant . fromInteger

Neg a => Neg (Diff a) where
  -- d(u-v) = du - dv
  (-) = arithmetic (-) (\_, _ => (1, -1))
  -- d(-x) = -1
  negate = elementary negate (const (-1))
