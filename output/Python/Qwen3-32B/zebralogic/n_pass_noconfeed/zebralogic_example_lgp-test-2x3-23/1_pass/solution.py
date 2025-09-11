import itertools
import json

# Generate all possible permutations for each category
names = list(itertools.permutations(['Eric', 'Arnold']))
children = list(itertools.permutations(['Bella', 'Fred']))
foods = list(itertools.permutations(['grilled cheese', 'pizza']))

# Iterate through all combinations of permutations
for name_perm in names:
    for child_perm in children:
        for food_perm in foods:
            # Check clue 1: The person who loves pizza is Arnold
            pizza_index = food_perm.index('pizza')
            if name_perm[pizza_index] != 'Arnold':
                continue
            
            # Check clue 2: Grilled cheese is directly left of Fred's house
            if food_perm[0] == 'grilled cheese' and child_perm[1] == 'Fred':
                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Food"],
                        "rows": [
                            ["1", name_perm[0], child_perm[0], food_perm[0]],
                            ["2", name_perm[1], child_perm[1], food_perm[1]]
                        ]
                    }
                }
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                exit()