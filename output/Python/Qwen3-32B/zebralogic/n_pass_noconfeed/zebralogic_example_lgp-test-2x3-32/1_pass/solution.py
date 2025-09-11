import itertools
import json

# Define possible values for each category
people = ['Eric', 'Arnold']
birthdays = ['april', 'sept']
colors = ['yellow', 'red']

solution = None

# Iterate through all permutations of the categories
for names in itertools.permutations(people):
    for birth in itertools.permutations(birthdays):
        for color in itertools.permutations(colors):
            # Check clue 1: Eric is the person who loves yellow
            eric_house_color = None
            if names[0] == 'Eric':
                eric_house_color = color[0]
            else:
                eric_house_color = color[1]
            if eric_house_color != 'yellow':
                continue

            # Check clue 2: The person with April birthday is in the first house
            if birth[0] != 'april':
                continue

            # Check clue 3: The person who loves yellow is not in the first house
            if color[0] == 'yellow':
                continue

            # Construct the solution if all clues are satisfied
            solution = {
                "solution": {
                    "header": ["House", "Name", "Birthday", "Color"],
                    "rows": [
                        ["1", names[0], birth[0], color[0]],
                        ["2", names[1], birth[1], color[1]]
                    ]
                }
            }
            # Break out of all loops once a solution is found
            break
        if solution:
            break
    if solution:
        break

# Output the solution as JSON
print(json.dumps(solution))