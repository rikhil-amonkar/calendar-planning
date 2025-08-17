import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Eric']
birthdays = ['april', 'sept']
mothers = ['Aniya', 'Holly']

solution_found = None

# Generate all permutations for each category
for name_perm in itertools.permutations(names):
    for birthday_perm in itertools.permutations(birthdays):
        # Check clue 2: The person whose birthday is in April is in the first house
        if birthday_perm[0] != 'april':
            continue
        for mother_perm in itertools.permutations(mothers):
            # Check clue 1: Eric is to the left of the person whose mother's name is Holly
            holly_index = mother_perm.index('Holly')
            holly_house = holly_index + 1  # Convert to 1-based index
            eric_index = name_perm.index('Eric')
            eric_house = eric_index + 1    # Convert to 1-based index
            
            if eric_house < holly_house:
                # Construct the solution in the required format
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Mother"],
                        "rows": [
                            [str(1), name_perm[0], birthday_perm[0], mother_perm[0]],
                            [str(2), name_perm[1], birthday_perm[1], mother_perm[1]]
                        ]
                    }
                }
                # Output the solution as JSON and exit
                print(json.dumps(solution_found))
                exit()