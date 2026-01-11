import itertools
import json

# Define the possible values
people = ['Alice', 'Arnold', 'Peter', 'Eric']
hair_colors = ['black', 'blonde', 'brown', 'red']
houses = [1, 2, 3, 4]

def is_valid_solution(person_assignment, hair_color_assignment):
    # Constraint 1: Eric is directly left of the person who has blonde hair.
    eric_index = person_assignment.index('Eric')
    blonde_index = hair_color_assignment.index('blonde')
    if eric_index + 1 != blonde_index:
        return False
    
    # Constraint 2: Alice and Arnold are next to each other.
    alice_index = person_assignment.index('Alice')
    arnold_index = person_assignment.index('Arnold')
    if abs(alice_index - arnold_index) != 1:
        return False
    
    # Constraint 3: Eric is the person who has brown hair.
    if hair_color_assignment[eric_index] != 'brown':
        return False
    
    # Constraint 4: The person who has black hair is not in the first house.
    if hair_color_assignment[0] == 'black':
        return False
    
    # Constraint 5: Alice is in the first house.
    if person_assignment[0] != 'Alice':
        return False
    
    return True

def solve_puzzle():
    # Generate all permutations of people and hair colors
    person_permutations = list(itertools.permutations(people))
    hair_color_permutations = list(itertools.permutations(hair_colors))
    
    # Check each combination of person and hair color permutations
    for person_assignment in person_permutations:
        for hair_color_assignment in hair_color_permutations:
            if is_valid_solution(person_assignment, hair_color_assignment):
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor"],
                        "rows": [
                            [str(house), person_assignment[i], hair_color_assignment[i]]
                            for i, house in enumerate(houses)
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())