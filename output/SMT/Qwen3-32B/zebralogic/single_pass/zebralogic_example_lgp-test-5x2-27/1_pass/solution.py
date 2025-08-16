from z3 import *

def solve_puzzle():
    solver = Solver()

    # Create variables for each house's name and height (houses 1-5, indexes 0-4)
    names = [Int(f'name_{i+1}') for i in range(5)]  # name_1 to name_5
    heights = [Int(f'height_{i+1}') for i in range(5)]  # height_1 to height_5

    # Clue 1: house 2's height is short (4)
    solver.add(heights[1] == 4)

    # Clue 7: house 5's height is average (1)
    solver.add(heights[4] == 1)

    # Clue 6: short (house 2) and very short are adjacent. So house 1 or 3 must be very short (3)
    solver.add(Or(heights[0] == 3, heights[2] == 3))  # house 1 is index 0, house 3 is index 2.

    # All names are distinct
    solver.add(Distinct(names))
    # All heights are distinct
    solver.add(Distinct(heights))

    # Names are in 0-4
    for n in names:
        solver.add(And(n >= 0, n <= 4))

    # Heights are in 0-4
    for h in heights:
        solver.add(And(h >= 0, h <= 4))

    # Clue 2: Peter (0) is directly left of Bob (2)
    clue2 = Or(
        And(names[0] == 0, names[1] == 2),
        And(names[1] == 0, names[2] == 2),
        And(names[2] == 0, names[3] == 2),
        And(names[3] == 0, names[4] == 2)
    )
    solver.add(clue2)

    # Clue 3: Eric (3) is to the left of Peter (0)
    clue3 = True
    for i in range(5):
        for j in range(5):
            clue3 = And(clue3, Implies(And(names[i] == 3, names[j] == 0), i < j))
    solver.add(clue3)

    # Clue 4: very tall (0) is directly left of Peter (0's position)
    clue4 = Or(
        And(heights[0] == 0, names[1] == 0),
        And(heights[1] == 0, names[2] == 0),
        And(heights[2] == 0, names[3] == 0),
        And(heights[3] == 0, names[4] == 0)
    )
    solver.add(clue4)

    # Clue 5: Alice (1) is directly left of average (house 5). So Alice is in house 4
    solver.add(names[3] == 1)  # house 4's name is Alice (index 3)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Extract the solution
        solution = []
        for i in range(5):
            house_num = i + 1
            name_val = model[names[i]].as_long()
            height_val = model[heights[i]].as_long()
            # Map name and height to strings
            name = {0: 'Peter', 1: 'Alice', 2: 'Bob', 3: 'Eric', 4: 'Arnold'}[name_val]
            height = {0: 'very tall', 1: 'average', 2: 'tall', 3: 'very short', 4: 'short'}[height_val]
            solution.append([str(house_num), name, height])
        return {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": solution
            }
        }
    else:
        return {"solution": {"header": [], "rows": []}}

# Call the function and print the JSON
import json
print(json.dumps(solve_puzzle(), indent=2))