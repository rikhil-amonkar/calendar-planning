from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    houses = range(1, 6)

    # Create a solver instance
    solver = Solver()

    # Declare variables
    name_vars = [[Bool(f'{name}_{house}') for house in houses] for name in names]
    mother_vars = [[Bool(f'{mother}_{house}') for house in houses] for mother in mothers]
    height_vars = [[Bool(f'{height}_{house}') for house in houses] for height in heights]

    # Each attribute is assigned to exactly one house
    for attr_vars in [name_vars, mother_vars, height_vars]:
        for attr_var in attr_vars:
            solver.add(Or(attr_var))
            for i in range(len(houses)):
                for j in range(i + 1, len(houses)):
                    solver.add(Not(And(attr_var[i], attr_var[j])))

    # Unique assignment per house
    for house in houses:
        solver.add(Sum([If(name_vars[name][house - 1], 1, 0) for name in range(len(names))]) == 1)
        solver.add(Sum([If(mother_vars[mother][house - 1], 1, 0) for mother in range(len(mothers))]) == 1)
        solver.add(Sum([If(height_vars[height][house - 1], 1, 0) for height in range(len(heights))]) == 1)

    # Clue 1: Alice is The person whose mother's name is Aniya.
    solver.add(name_vars[names.index('Alice')][houses.index(1)] == mother_vars[mothers.index('Aniya')][houses.index(1)])

    # Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    for i in range(len(houses) - 1):
        for j in range(i + 1, len(houses)):
            solver.add(Or(Not(height_vars[heights.index('average')][i]), Not(mother_vars[mothers.index('Penny')][j])))

    # Clue 3: The person whose mother's name is Janelle is Bob.
    solver.add(mother_vars[mothers.index('Janelle')][houses.index(1)] == name_vars[names.index('Bob')][houses.index(1)])

    # Clue 4: Peter is not in the second house.
    solver.add(Not(name_vars[names.index('Peter')][houses.index(2)]))

    # Clue 5: The person who is short is directly left of Arnold.
    for i in range(len(houses) - 1):
        solver.add(Implies(height_vars[heights.index('short')][i], name_vars[names.index('Arnold')][i + 1]))

    # Clue 6: The person who is very tall is Arnold.
    solver.add(height_vars[heights.index('very tall')][houses.index(1)] == name_vars[names.index('Arnold')][houses.index(1)])

    # Clue 7: Bob is directly left of the person who has an average height.
    for i in range(len(houses) - 1):
        solver.add(Implies(name_vars[names.index('Bob')][i], height_vars[heights.index('average')][i + 1]))

    # Clue 8: Eric is not in the fifth house.
    solver.add(Not(name_vars[names.index('Eric')][houses.index(5)]))

    # Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    for i in range(1, len(houses)):
        for j in range(i):
            solver.add(Or(Not(height_vars[heights.index('very tall')][i]), Not(mother_vars[mothers.index('Holly')][j])))

    # Clue 10: Eric is The person whose mother's name is Kailyn.
    solver.add(name_vars[names.index('Eric')][houses.index(1)] == mother_vars[mothers.index('Kailyn')][houses.index(1)])

    # Clue 11: The person who is very short is in the fifth house.
    solver.add(height_vars[heights.index('very short')][houses.index(5)])

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = next(name for name, var in zip(names, name_vars) if model.evaluate(var[house - 1]))
            mother = next(mother for mother, var in zip(mothers, mother_vars) if model.evaluate(var[house - 1]))
            height = next(height for height, var in zip(heights, height_vars) if model.evaluate(var[house - 1]))
            solution.append([str(house), name, mother, height])
        
        return {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": solution
            }
        }

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))