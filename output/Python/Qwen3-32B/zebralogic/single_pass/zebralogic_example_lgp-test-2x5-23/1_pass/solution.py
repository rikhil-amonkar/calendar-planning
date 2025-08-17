import itertools
import json

# Define the categories
categories = {
    'Name': ['Arnold', 'Eric'],
    'Education': ['associate', 'high school'],
    'Height': ['short', 'very short'],
    'Food': ['grilled cheese', 'pizza'],
    'Drink': ['tea', 'water']
}

# Generate all permutations for each category
perms = []
for key in categories:
    perms.append(list(itertools.permutations(categories[key])))

found = False
solution_data = None

# Iterate through all possible combinations of permutations
for possibility in itertools.product(*perms):
    names, education, heights, foods, drinks = possibility

    # Find Arnold's house
    arnold_house = -1
    for i in range(2):
        if names[i] == 'Arnold':
            arnold_house = i
            break
    if arnold_house == -1:
        continue  # This should not happen as Arnold is in the Name list

    # Check if Arnold's food is pizza (constraint 5)
    if foods[arnold_house] != 'pizza':
        continue

    # Check all constraints
    valid = True

    # Constraint 1: very short is pizza lover
    for i in range(2):
        if heights[i] == 'very short' and foods[i] != 'pizza':
            valid = False
            break

    # Constraint 2: grilled cheese in second house
    if foods[1] != 'grilled cheese':
        valid = False

    # Constraint 3: high school is pizza lover
    for i in range(2):
        if education[i] == 'high school' and foods[i] != 'pizza':
            valid = False
            break

    # Constraint 4: tea drinker loves grilled cheese
    for i in range(2):
        if drinks[i] == 'tea' and foods[i] != 'grilled cheese':
            valid = False
            break

    if valid:
        # Build the solution
        rows = []
        for i in [0, 1]:
            house_num = str(i + 1)
            name = names[i]
            edu = education[i]
            height = heights[i]
            food = foods[i]
            drink = drinks[i]
            rows.append([house_num, name, edu, height, food, drink])
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": rows
            }
        }
        found = True
        break  # Exit the loop once a solution is found

if found:
    print(json.dumps(solution_data, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))