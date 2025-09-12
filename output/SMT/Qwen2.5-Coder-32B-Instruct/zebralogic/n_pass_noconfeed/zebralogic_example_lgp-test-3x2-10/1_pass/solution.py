from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['short', 'very short', 'average']
    houses = [1, 2, 3]

    # Create symbolic variables for each house
    house_name = [String(f'house_{i}_name') for i in houses]
    house_height = [String(f'house_{i}_height') for i in houses]

    # Create the solver
    solver = Solver()

    # Add constraints for unique names and heights per house
    solver.add(Distinct(house_name))
    solver.add(Distinct(house_height))

    # Add constraints for each clue
    # Clue 1: Eric is not in the first house.
    solver.add(house_name[0] != 'Eric')

    # Clue 2: The person who is very short is somewhere to the left of the person who is short.
    solver.add(Or(house_height[0] == 'very short', And(house_height[0] != 'short', Or(house_height[1] == 'very short', And(house_height[1] != 'short', house_height[2] == 'very short')))))

    # Clue 3: The person who is very short is Eric.
    solver.add(Or(house_name[0] == 'Eric' and house_height[0] == 'very short', house_name[1] == 'Eric' and house_height[1] == 'very short', house_name[2] == 'Eric' and house_height[2] == 'very short'))

    # Clue 4: Arnold is not in the first house.
    solver.add(house_name[0] != 'Arnold')

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        for house in houses:
            name = model[house_name[house-1]].as_string()[1:-1]
            height = model[house_height[house-1]].as_string()[1:-1]
            solution["solution"]["rows"].append([str(house), name, height])
        return solution
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))