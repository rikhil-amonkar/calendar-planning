from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4, 5]
    names = ['Peter', 'Alice', 'Bob', 'Eric', 'Arnold']
    heights = ['very tall', 'average', 'tall', 'very short', 'short']

    # Create variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    height_vars = {house: Int(f'height_{house}') for house in houses}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for house in houses:
        solver.add(name_vars[house] >= 0)
        solver.add(name_vars[house] < len(names))
        solver.add(height_vars[house] >= 0)
        solver.add(height_vars[house] < len(heights))

    # All names and heights must be unique
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([height_vars[house] for house in houses]))

    # Clue constraints
    # 1. The person who is short is in the second house.
    solver.add(height_vars[2] == heights.index('short'))

    # 2. Peter is directly left of Bob.
    solver.add(If(name_vars[1] == names.index('Peter'), name_vars[2] == names.index('Bob'), True))
    solver.add(If(name_vars[2] == names.index('Peter'), name_vars[3] == names.index('Bob'), True))
    solver.add(If(name_vars[3] == names.index('Peter'), name_vars[4] == names.index('Bob'), True))

    # 3. Eric is somewhere to the left of Peter.
    solver.add(Or(
        And(name_vars[1] == names.index('Eric'), name_vars[2] != names.index('Eric'), name_vars[3] != names.index('Eric'), name_vars[4] != names.index('Eric'), name_vars[5] != names.index('Eric')),
        And(name_vars[2] == names.index('Eric'), name_vars[3] != names.index('Eric'), name_vars[4] != names.index('Eric'), name_vars[5] != names.index('Eric')),
        And(name_vars[3] == names.index('Eric'), name_vars[4] != names.index('Eric'), name_vars[5] != names.index('Eric')),
        And(name_vars[4] == names.index('Eric'))
    ))
    solver.add(Or(
        name_vars[1] == names.index('Peter'),
        name_vars[2] == names.index('Peter'),
        name_vars[3] == names.index('Peter'),
        name_vars[4] == names.index('Peter')
    ))

    # 4. The person who is very tall is directly left of Peter.
    solver.add(If(name_vars[1] == names.index('Peter'), height_vars[1] == heights.index('very tall'), True))
    solver.add(If(name_vars[2] == names.index('Peter'), height_vars[2] == heights.index('very tall'), True))
    solver.add(If(name_vars[3] == names.index('Peter'), height_vars[3] == heights.index('very tall'), True))
    solver.add(If(name_vars[4] == names.index('Peter'), height_vars[4] == heights.index('very tall'), True))

    # 5. Alice is directly left of the person who has an average height.
    solver.add(If(name_vars[1] == names.index('Alice'), height_vars[2] == heights.index('average'), True))
    solver.add(If(name_vars[2] == names.index('Alice'), height_vars[3] == heights.index('average'), True))
    solver.add(If(name_vars[3] == names.index('Alice'), height_vars[4] == heights.index('average'), True))
    solver.add(If(name_vars[4] == names.index('Alice'), height_vars[5] == heights.index('average'), True))

    # 6. The person who is short and the person who is very short are next to each other.
    solver.add(Or(
        And(height_vars[1] == heights.index('short'), height_vars[2] == heights.index('very short')),
        And(height_vars[2] == heights.index('short'), height_vars[1] == heights.index('very short')),
        And(height_vars[2] == heights.index('short'), height_vars[3] == heights.index('very short')),
        And(height_vars[3] == heights.index('short'), height_vars[2] == heights.index('very short')),
        And(height_vars[3] == heights.index('short'), height_vars[4] == heights.index('very short')),
        And(height_vars[4] == heights.index('short'), height_vars[3] == heights.index('very short')),
        And(height_vars[4] == heights.index('short'), height_vars[5] == heights.index('very short')),
        And(height_vars[5] == heights.index('short'), height_vars[4] == heights.index('very short'))
    ))

    # 7. The person who has an average height is in the fifth house.
    solver.add(height_vars[5] == heights.index('average'))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        for house in houses:
            name = names[model[name_vars[house]].as_long()]
            height = heights[model[height_vars[house]].as_long()]
            solution["solution"]["rows"].append([str(house), name, height])
        return solution
    else:
        return None

import json
print(json.dumps(solve_puzzle(), indent=2))