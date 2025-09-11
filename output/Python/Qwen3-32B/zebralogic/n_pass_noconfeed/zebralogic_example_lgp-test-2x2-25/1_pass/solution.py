import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Eric']
vacations = ['beach', 'mountain']

# Generate all possible permutations for names and vacations
for name_perm in itertools.permutations(names):
    for vac_perm in itertools.permutations(vacations):
        # Check clue: Arnold is to the right of the beach lover
        beach_house = vac_perm.index('beach') + 1  # Convert 0-based index to house number (1-based)
        arnold_house = name_perm.index('Arnold') + 1  # Convert 0-based index to house number
        if arnold_house > beach_house:
            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation"],
                    "rows": []
                }
            }
            # Populate the rows with the correct data
            for i in range(2):
                house_num = i + 1
                name = name_perm[i]
                vacation = vac_perm[i]
                solution['solution']['rows'].append([str(house_num), name, vacation])
            # Output the solution as JSON
            print(json.dumps(solution))
            exit()