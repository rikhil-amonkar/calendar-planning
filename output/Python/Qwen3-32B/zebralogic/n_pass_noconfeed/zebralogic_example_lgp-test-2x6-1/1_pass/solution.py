import itertools
import json

# Generate all permutations for each category
name_perms = list(itertools.permutations(['Arnold', 'Eric']))
sport_perms = list(itertools.permutations(['basketball', 'soccer']))
hair_perms = list(itertools.permutations(['brown', 'black']))
height_perms = list(itertools.permutations(['very short', 'short']))
smoothie_perms = list(itertools.permutations(['desert', 'cherry']))
flower_perms = list(itertools.permutations(['daffodils', 'carnations']))

all_combinations = itertools.product(
    name_perms, 
    sport_perms, 
    hair_perms, 
    height_perms, 
    smoothie_perms, 
    flower_perms
)

solution_found = None

for combination in all_combinations:
    name_p, sport_p, hair_p, height_p, smoothie_p, flower_p = combination

    # Check clue 1: soccer is in house 1
    if sport_p[0] != 'soccer':
        continue

    # Check clue 2: desert in house 1 and very short in house 2
    if smoothie_p[0] != 'desert' or height_p[1] != 'very short':
        continue

    # Check clue 3: very short (house 2) has brown hair
    if hair_p[1] != 'brown':
        continue

    # Check clue 4: desert lover (house 1) has carnations
    if flower_p[0] != 'carnations':
        continue

    # Check clue 5: Eric (house 1) is next to brown hair (house 2)
    if name_p[0] != 'Eric':
        continue

    solution_found = combination
    break  # Assuming only one valid solution

# Construct the solution JSON
if solution_found:
    name_p, sport_p, hair_p, height_p, smoothie_p, flower_p = solution_found
    rows = [
        [
            "1", name_p[0], sport_p[0], hair_p[0], height_p[0], 
            smoothie_p[0], flower_p[0]
        ],
        [
            "2", name_p[1], sport_p[1], hair_p[1], height_p[1], 
            smoothie_p[1], flower_p[1]
        ]
    ]
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))
else:
    print(json.dumps({"solution": "No solution found"}))