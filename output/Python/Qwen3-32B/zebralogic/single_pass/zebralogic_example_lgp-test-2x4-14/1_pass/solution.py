import itertools
import json

# Generate all possible permutations for each category
names_list = list(itertools.permutations(['Eric', 'Arnold']))
house_styles_list = list(itertools.permutations(['victorian', 'colonial']))
smoothies_list = list(itertools.permutations(['cherry', 'desert']))
pets_list = list(itertools.permutations(['dog', 'cat']))

solution_found = None

for names in names_list:
    for house_styles in house_styles_list:
        for smoothies in smoothies_list:
            for pets in pets_list:
                # Check constraints
                valid = True

                # Constraint 1: Cherry smoothie <-> dog
                for i in range(2):
                    if smoothies[i] == 'cherry' and pets[i] != 'dog':
                        valid = False
                        break
                    if pets[i] == 'dog' and smoothies[i] != 'cherry':
                        valid = False
                        break

                # Constraint 2: Victorian house has dog
                victorian_index = None
                for i in range(2):
                    if house_styles[i] == 'victorian':
                        victorian_index = i
                        if pets[i] != 'dog':
                            valid = False
                            break

                if victorian_index is None:
                    # No victorian house? Impossible since it's a permutation
                    valid = False

                if not valid:
                    continue

                # Constraint 3: Victorian is left of Eric
                eric_index = names.index('Eric')
                if victorian_index >= eric_index:
                    valid = False

                if valid:
                    # Build the solution
                    solution_found = [
                        ["1", names[0], house_styles[0], smoothies[0], pets[0]],
                        ["2", names[1], house_styles[1], smoothies[1], pets[1]]
                    ]
                    # Break out of loops
                    break

            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Construct the JSON output
output = {
    "solution": {
        "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
        "rows": solution_found
    }
}

print(json.dumps(output, indent=2))