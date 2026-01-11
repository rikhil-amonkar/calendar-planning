import itertools
import json

def solve_puzzle():
    # Define the variables
    houses = [1, 2, 3]
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']

    # Generate all permutations of names and heights
    for name_permutation in itertools.permutations(names):
        for height_permutation in itertools.permutations(heights):
            # Create a dictionary to store the assignment
            assignment = {house: {'name': name, 'height': height} 
                          for house, name, height in zip(houses, name_permutation, height_permutation)}
            
            # Check constraints
            # Constraint 1: Peter is somewhere to the right of Eric
            if assignment[1]['name'] == 'Peter' or (assignment[1]['name'] == 'Eric' and assignment[2]['name'] == 'Peter'):
                continue
            if assignment[2]['name'] == 'Eric' and assignment[3]['name'] != 'Peter':
                continue
            
            # Constraint 2: The person who is short is in the first house
            if assignment[1]['height'] != 'short':
                continue
            
            # Constraint 3: There is one house between the person who is short and the person who is very short
            if assignment[3]['height'] != 'very short':
                continue
            
            # Constraint 4: Arnold and the person who is very short are next to each other
            if assignment[2]['name'] != 'Arnold' and assignment[2]['height'] != 'very short':
                continue
            
            # If all constraints are satisfied, format the solution
            rows = [[str(house), assignment[house]['name'], assignment[house]['height']] for house in houses]
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": rows
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())