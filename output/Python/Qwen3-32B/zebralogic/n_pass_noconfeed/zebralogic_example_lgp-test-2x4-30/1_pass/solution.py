import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Eric']
hair_colors = ['black', 'brown']
sports = ['basketball', 'soccer']
smoothies = ['desert', 'cherry']

solution_found = None

# Iterate through all permutations of attributes
for name_perm in itertools.permutations(names):
    for hair_perm in itertools.permutations(hair_colors):
        for sport_perm in itertools.permutations(sports):
            for smoothie_perm in itertools.permutations(smoothies):
                # Check constraint 1: The Desert smoothie lover is Arnold
                desert_index = None
                for i in [0, 1]:
                    if smoothie_perm[i] == 'desert':
                        desert_index = i
                if name_perm[desert_index] != 'Arnold':
                    continue

                # Check constraint 2: Brown hair loves basketball
                brown_index = None
                for i in [0, 1]:
                    if hair_perm[i] == 'brown':
                        brown_index = i
                if sport_perm[brown_index] != 'basketball':
                    continue

                # Check constraint 3: Arnold is to the left of black hair
                arnold_idx = name_perm.index('Arnold')
                black_idx = hair_perm.index('black')
                if not (arnold_idx < black_idx):
                    continue

                # Build the solution if all constraints are satisfied
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                        "rows": [
                            ["1", name_perm[0], hair_perm[0], sport_perm[0], smoothie_perm[0]],
                            ["2", name_perm[1], hair_perm[1], sport_perm[1], smoothie_perm[1]]
                        ]
                    }
                }
                # Break out of all loops once solution is found
                break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found))