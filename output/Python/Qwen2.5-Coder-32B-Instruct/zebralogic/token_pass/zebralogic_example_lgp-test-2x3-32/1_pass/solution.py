import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ['Eric', 'Arnold']
    birthdays = ['sept', 'april']
    colors = ['yellow', 'red']

    # Generate all possible combinations for the two houses
    all_combinations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(colors))

    # Filter out the invalid combinations based on the constraints
    valid_solutions = []
    for combination in all_combinations:
        # Unpack the combination into two houses
        house1 = {'Name': combination[0], 'Birthday': combination[2], 'Color': combination[4]}
        house2 = {'Name': combination[1], 'Birthday': combination[3], 'Color': combination[5]}

        # Apply the constraints
        if (house2['Name'] == 'Eric' and house2['Color'] == 'yellow' and
            house1['Birthday'] == 'april' and
            house2['Color'] != 'yellow'):
            valid_solutions.append([house1, house2])

    # There should be only one valid solution
    if len(valid_solutions) != 1:
        raise ValueError("No unique solution found!")

    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [
                ["1", valid_solutions[0][0]['Name'], valid_solutions[0][0]['Birthday'], valid_solutions[0][0]['Color']],
                ["2", valid_solutions[0][1]['Name'], valid_solutions[0][1]['Birthday'], valid_solutions[0][1]['Color']]
            ]
        }
    }

    # Convert the solution to a JSON-formatted string
    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())