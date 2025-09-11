import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']

    # Generate all possible permutations for the assignments
    for name_perm in itertools.permutations(names):
        for pet_perm in itertools.permutations(pets):
            # Unpack the permutations for easier reference
            house_1_name, house_2_name, house_3_name, house_4_name = name_perm
            house_1_pet, house_2_pet, house_3_pet, house_4_pet = pet_perm

            # Check all the clues
            if (names.index('Alice') < names.index('Peter') and  # Clue 1
                names.index('Eric') != 0 and                      # Clue 2
                names.index('Eric') == pets.index('bird') and     # Clue 3
                abs(names.index('Peter') - pets.index('fish')) == 2 and  # Clue 4
                names.index('Alice') != 0 and                     # Clue 5
                pets.index('fish') == names.index('Arnold')):       # Clue 6
                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet"],
                        "rows": [
                            ["1", house_1_name, house_1_pet],
                            ["2", house_2_name, house_2_pet],
                            ["3", house_3_name, house_3_pet],
                            ["4", house_4_name, house_4_pet]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Print the solution in JSON format
print(solve_puzzle())