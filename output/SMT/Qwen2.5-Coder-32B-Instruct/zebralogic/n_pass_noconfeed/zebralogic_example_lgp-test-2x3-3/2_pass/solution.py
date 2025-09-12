from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']
    houses = [1, 2]

    # Create symbolic variables
    name_vars = [[String(f'name_{h}_{n}') for n in range(2)] for h in houses]
    food_vars = [[String(f'food_{h}_{f}') for f in range(2)] for h in houses]
    mother_vars = [[String(f'mother_{h}_{m}') for m in range(2)] for h in houses]

    # Create the solver
    solver = Solver()

    # Add constraints for unique values per category within each house
    for h in houses:
        solver.add(Distinct([name_vars[h-1][n] for n in range(2)]))
        solver.add(Distinct([food_vars[h-1][f] for f in range(2)]))
        solver.add(Distinct([mother_vars[h-1][m] for m in range(2)]))

    # Add constraints for unique values across houses
    solver.add(Distinct([name_vars[h-1][n] for h in houses for n in range(2)]))
    solver.add(Distinct([food_vars[h-1][f] for h in houses for f in range(2)]))
    solver.add(Distinct([mother_vars[h-1][m] for h in houses for m in range(2)]))

    # Add specific constraints from the clues
    # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
    solver.add(Or(
        And(food_vars[0][0] == 'grilled cheese', food_vars[0][1] == 'pizza'),
        And(food_vars[1][0] == 'grilled cheese', food_vars[1][1] == 'pizza')
    ))

    # Clue 2: Arnold is not in the second house.
    solver.add(name_vars[1][0] != 'Arnold')
    solver.add(name_vars[1][1] != 'Arnold')

    # Clue 3: Arnold is The person whose mother's name is Holly.
    solver.add(Or(
        And(name_vars[0][0] == 'Arnold', mother_vars[0][0] == 'Holly'),
        And(name_vars[0][1] == 'Arnold', mother_vars[0][1] == 'Holly')
    ))

    # Assign possible values to variables
    for h in houses:
        for n in range(2):
            solver.add(Or([name_vars[h-1][n] == name for name in names]))
            solver.add(Or([food_vars[h-1][n] == food for food in foods]))
            solver.add(Or([mother_vars[h-1][n] == mother for mother in mothers]))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": []
            }
        }
        for h in houses:
            for n in range(2):
                name = model.evaluate(name_vars[h-1][n]).as_string().strip('"')
                food = model.evaluate(food_vars[h-1][n]).as_string().strip('"')
                mother = model.evaluate(mother_vars[h-1][n]).as_string().strip('"')
                solution["solution"]["rows"].append([str(h), name, food, mother])
        return solution
    else:
        return None

# Solve the puzzle and print the solution in JSON format
import json
solution = solve_puzzle()
if solution:
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")