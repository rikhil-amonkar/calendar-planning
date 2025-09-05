import json
from z3 import *

def main():
    solver = Solver()
    
    names = ['Eric', 'Arnold']
    books = ['science fiction', 'mystery']
    birthdays = ['april', 'sept']
    animals = ['horse', 'cat']
    
    n1, n2 = Ints('n1 n2')
    b1, b2 = Ints('b1 b2')
    bir1, bir2 = Ints('bir1 bir2')
    a1, a2 = Ints('a1 a2')
    
    variables = [n1, n2, b1, b2, bir1, bir2, a1, a2]
    for var in variables:
        solver.add(var >= 0, var <= 1)
    
    solver.add(Distinct(n1, n2))
    solver.add(Distinct(b1, b2))
    solver.add(Distinct(bir1, bir2))
    solver.add(Distinct(a1, a2))
    
    solver.add(n1 == 0)
    solver.add(bir1 == 1)
    solver.add(b2 == 0)
    solver.add((a1 == 0) == (bir1 == 1))
    solver.add((a2 == 0) == (bir2 == 1))
    
    if solver.check() == sat:
        model = solver.model()
        n1_val = model.evaluate(n1).as_long()
        n2_val = model.evaluate(n2).as_long()
        b1_val = model.evaluate(b1).as_long()
        b2_val = model.evaluate(b2).as_long()
        bir1_val = model.evaluate(bir1).as_long()
        bir2_val = model.evaluate(bir2).as_long()
        a1_val = model.evaluate(a1).as_long()
        a2_val = model.evaluate(a2).as_long()
        
        row1 = ["1", names[n1_val], books[b1_val], birthdays[bir1_val], animals[a1_val]]
        row2 = ["2", names[n2_val], books[b2_val], birthdays[bir2_val], animals[a2_val]]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                "rows": [row1, row2]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()