
def combine(f: (Int, Int) => Int, unit: Int)(g: Int => Int)(a: Int, b: Int): Int =
  if (a > b) unit
  else f(g(a), combine(f, unit)(g)(a + 1, b))

def sum(f: Int => Int)(a: Int, b: Int) = combine((x, y) => x + y, 0)(f)(a, b)

def sumCubes(a: Int, b: Int) = sum(x => x * x)(a, b)

sumCubes(1, 3)