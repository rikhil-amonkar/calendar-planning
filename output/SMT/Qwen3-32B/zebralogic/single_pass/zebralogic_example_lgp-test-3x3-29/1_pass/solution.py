from z3 import *
import json

def solve_puzzle():
    # Create variables for each house (1, 2, 3)
    n1, n2, n3 = Ints('n1 n2 n3')  # names: 0=Eric, 1=Peter, 2=Arnold
    m1, m2, m3 = Ints('m1 m2 m3')  # mothers: 0=Holly, 1=Aniya, 2=Janelle
    f1, f2, f3 = Ints('f1 f2 f3')  # foods: 0=pizza, 1=grilled cheese, 2=spaghetti

    solver = Solver()

    # All different constraints
    solver.add(Distinct([n1, n2, n3]))
    solver.add(Distinct([m1, m2, m3]))
    solver.add(Distinct([f1, f2, f3]))

    # Variables are in 0-2
    for var in [n1, n2, n3, m1, m2, m3, f1, f2, f3]:
        solver.add(And(var >= 0, var <= 2))

    # Clue 3: Eric (0) has food grilled cheese (1)
    solver.add(Implies(n1 == 0, f1 == 1))
    solver.add(Implies(n2 == 0, f2 == 1))
    solver.add(Implies(n3 == 0, f3 == 1))

    # Clue 4: Peter (1) has mother Holly (0)
    solver.add(Implies(n1 == 1, m1 == 0))
    solver.add(Implies(n2 == 1, m2 == 0))
    solver.add(Implies(n3 == 1, m3 == 0))

    # Clue 2: Eric's house is directly left of Aniya's (mother 1)
    solver.add(Implies(n1 == 0, m2 == 1))
    solver.add(Implies(n2 == 0, m3 == 1))
    solver.add(n3 != 0)  # Eric can't be in house 3

    # Clue 1: Spaghetti (2) and Peter (1) are adjacent
    solver.add(Implies(f1 == 2, n2 == 1))  # if spaghetti in 1, Peter in 2
    solver.add(Implies(f2 == 2, Or(n1 == 1, n3 == 1)))  # if in 2, Peter in 1 or 3
    solver.add(Implies(f3 == 2, n2 == 1))  # if in 3, Peter in 2

    # Check if satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Extract values
        names = [model.eval(n1).as_long(), model.eval(n2).as_long(), model.eval(n3).as_long()]
        mothers = [model.eval(m1).as_long(), model.eval(m2).as_long(), model.eval(m3).as_long()]
        foods = [model.eval(f1).as_long(), model.eval(f2).as_long(), model.eval(f3).as_long()]

        # Map to strings
        name_map = {0: 'Eric', 1: 'Peter', 2: 'Arnold'}
        mother_map = {0: 'Holly', 1: 'Aniya', 2: 'Janelle'}
        food_map = {0: 'pizza', 1: 'grilled cheese', 2: 'spaghetti'}

        rows = []
        for i in range(3):
            house_num = i + 1
            name = name_map[names[i]]
            mother = mother_map[mothers[i]]
            food = food_map[foods[i]]
            rows.append([str(house_num), name, mother, food])

        return {
            "solution": {
                "header": ["House", "Name", "Mother", "Food"],
                "rows": rows
            }
        }
    else:
        return {"solution": "No solution found."}

# Generate and print the JSON output
solution = solve_puzzle()
print(json.dumps(solution, indent=2))