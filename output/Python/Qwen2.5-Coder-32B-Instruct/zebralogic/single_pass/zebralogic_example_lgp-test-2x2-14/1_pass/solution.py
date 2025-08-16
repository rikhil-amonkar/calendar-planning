import json

def solve_puzzle():
    # Define the possible values
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    foods = ['pizza', 'grilled cheese']

    # Initialize the solution grid
    solution_grid = []

    # Iterate over all possible permutations
    for name1 in names:
        for food1 in foods:
            for name2 in names:
                if name2 != name1:  # Ensure different names
                    for food2 in foods:
                        if food2 != food1:  # Ensure different foods
                            # Apply the clues
                            if food2 == 'pizza' and name2 != 'Arnold':
                                solution_grid.append([houses[0], name1, food1])
                                solution_grid.append([houses[1], name2, food2])

    # Format the solution as JSON
    solution_json = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": solution_grid
        }
    }

    return json.dumps(solution_json, indent=2)

# Output the solution
print(solve_puzzle())