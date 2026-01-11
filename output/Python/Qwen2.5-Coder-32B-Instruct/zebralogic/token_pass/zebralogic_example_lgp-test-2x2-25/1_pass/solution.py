import itertools
import json

def solve_puzzle():
    # Define the variables
    houses = [1, 2]
    people = ['Arnold', 'Eric']
    vacations = ['beach', 'mountain']
    
    # Generate all possible combinations of people and vacations for the two houses
    all_combinations = list(itertools.permutations(people)) * list(itertools.permutations(vacations))
    
    # Filter combinations based on the constraint
    valid_combinations = []
    for people_combination in itertools.permutations(people):
        for vacation_combination in itertools.permutations(vacations):
            # Create a dictionary for the current combination
            combination_dict = {
                houses[0]: {'Name': people_combination[0], 'Vacation': vacation_combination[0]},
                houses[1]: {'Name': people_combination[1], 'Vacation': vacation_combination[1]}
            }
            
            # Check the constraint: Arnold is somewhere to the right of the person who loves beach vacations
            if (combination_dict[1]['Name'] == 'Arnold' and combination_dict[2]['Vacation'] == 'beach') or \
               (combination_dict[2]['Name'] == 'Arnold' and combination_dict[1]['Vacation'] != 'beach'):
                valid_combinations.append(combination_dict)
    
    # Since there should be only one valid combination, we take the first one
    if valid_combinations:
        solution = valid_combinations[0]
    else:
        raise ValueError("No valid solution found.")
    
    # Format the solution as a JSON object
    json_solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": [
                [str(house), solution[house]['Name'], solution[house]['Vacation']] for house in houses
            ]
        }
    }
    
    return json.dumps(json_solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())