import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    houses = ['1', '2']
    names = ['Eric', 'Arnold']
    foods = ['pizza', 'grilled cheese']
    
    # Generate all possible permutations of assignments
    all_permutations = list(itertools.permutations(names)) * len(foods)
    food_permutations = list(itertools.permutations(foods))
    
    # Initialize the solution variable
    solution = None
    
    # Iterate over all possible combinations of name and food assignments
    for name_assignment in itertools.permutations(names):
        for food_assignment in itertools.permutations(foods):
            # Create a dictionary to hold the current assignment
            assignment = {
                '1': {'name': name_assignment[0], 'food': food_assignment[0]},
                '2': {'name': name_assignment[1], 'food': food_assignment[1]}
            }
            
            # Check the constraints
            if (assignment['2']['food'] == 'pizza' and  # Constraint 1
                assignment['1']['name'] != 'Arnold'):     # Constraint 2
                solution = assignment
                break
        if solution:
            break
    
    # Format the solution as required
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": [
                ["1", solution['1']['name'], solution['1']['food']],
                ["2", solution['2']['name'], solution['2']['food']]
            ]
        }
    }
    
    # Convert the solution to JSON
    return json.dumps(formatted_solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())