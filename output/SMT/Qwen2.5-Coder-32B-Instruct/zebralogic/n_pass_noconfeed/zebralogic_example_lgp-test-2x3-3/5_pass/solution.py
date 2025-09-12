from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']
    houses = [1, 2]

    # Create symbolic variables
    name_vars = [[Int(f'name_{h}_{n}') for n in range(2)] for h in houses]
    food_vars = [[Int(f'food_{h}_{f}') for f in range(2)] for h in houses]
    mother_vars = [[Int(f'mother_{h}_{m}') for m in range(2)] for h in houses]

    # Create the solver
    solver = Solver()

    # Map names, foods, and mothers to integers
    name_map = {name: i for i, name in enumerate(names)}
    food_map = {food: i for i, food in enumerate(foods)}
    mother_map = {mother: i for i, mother in enumerate(mothers)}

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
        And(food_vars[0][0] == food_map['grilled cheese'], food_vars[0][1] == food_map['pizza']),
        And(food_vars[1][0] == food_map['grilled cheese'], food_vars[1][1] == food_map['pizza'])
    ))

    # Clue 2: Arnold is not in the second house.
    solver.add(name_vars[1][0] != name_map['Arnold'])
    solver.add(name_vars[1][1] != name_map['Arnold'])

    # Clue 3: Arnold is the person whose mother's name is Holly.
    solver.add(Or(
        And(name_vars[0][0] == name_map['Arnold'], mother_vars[0][0] == mother_map['Holly']),
        And(name_vars[0][1] == name_map['Arnold'], mother_vars[0][1] == mother_map['Holly'])
    ))

    # Clue 4: Eric is the other person.
    solver.add(Or(
        And(name_vars[0][0] == name_map['Eric'], mother_vars[0][0] == mother_map['Aniya']),
        And(name_vars[0][1] == name_map['Eric'], mother_vars[0][1] == mother_map['Aniya'])
    ))

    # Assign possible values to variables
    for h in houses:
        for n in range(2):
            solver.add(name_vars[h-1][n] >= 0)
            solver.add(name_vars[h-1][n] < len(names))
            solver.add(food_vars[h-1][n] >= 0)
            solver.add(food_vars[h-1][n] < len(foods))
            solver.add(mother_vars[h-1][n] >= 0)
            solver.add(mother_vars[h-1][n] < len(mothers))

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
                name = names[model.evaluate(name_vars[h-1][n]).as_long()]
                food = foods[model.evaluate(food_vars[h-1][n]).as_long()]
                mother = mothers[model.evaluate(mother_vars[h-1][n]).as_long()]
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