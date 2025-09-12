import z3

c1, c2, c3, c4, c5 = z3.Ints('c1 c2 c3 c4 c5')
s = z3.Solver()
s.add(c1 == 1, c2 == 2, c3 == 3, c4 == 4, c5 == 5)

if s.check() == z3.sat:
    model = s.model()
    cities = [model.eval(c).as_long() for c in [c1, c2, c3, c4, c5]]
    print(cities)
else:
    print("No solution found.")