from z3 import Solver, Int, sat, model

c1, c2, c3, c4, c5 = Ints('c1 c2 c3 c4 c5')
s = Solver()
# Add your actual constraints here
s.add(c1 == 1, c2 == 2, c3 == 3, c4 == 4, c5 == 5)

if s.check() == sat:
    model = s.model()
    cities = [model.eval(c1), model.eval(c2), model.eval(c3), model.eval(c4), model.eval(c5)]
    cities = [c.as_long() for c in cities]
    print(cities)
else:
    print("No solution found.")