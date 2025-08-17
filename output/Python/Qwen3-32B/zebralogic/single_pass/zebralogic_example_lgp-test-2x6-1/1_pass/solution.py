import itertools
import json

# Define the categories and their possible values
categories = [
    ('Name', ['Arnold', 'Eric']),
    ('FavoriteSport', ['basketball', 'soccer']),
    ('HairColor', ['brown', 'black']),
    ('Height', ['very short', 'short']),
    ('Smoothie', ['desert', 'cherry']),
    ('Flower', ['daffodils', 'carnations']),
]

# Generate all possible permutations for each category
all_perms = []
for category in categories:
    _, items = category
    perms = list(itertools.permutations(items))
    all_perms.append(perms)

solution_found = None

# Iterate through all possible combinations of permutations
for perm_combo in itertools.product(*all_perms):
    # Unpack permutations for each category
    name_perm, sport_perm, hair_perm, height_perm, smoothie_perm, flower_perm = perm_combo

    # Check all constraints
    # Clue 1: Soccer is not in the second house
    if sport_perm[0] != 'soccer':
        continue

    # Clue 2: Desert smoothie lover is directly left of the very short person
    if smoothie_perm[0] != 'desert' or height_perm[1] != 'very short':
        continue

    # Clue 3: Very short person has brown hair
    if hair_perm[1] != 'brown':
        continue

    # Clue 4: Carnations lover is the Desert smoothie lover
    if flower_perm[0] != 'carnations':
        continue

    # Clue 5: Eric and the person with brown hair are next to each other
    if name_perm[0] != 'Eric':
        continue

    # Build the solution if all constraints are satisfied
    rows = [
        [
            "1",
            name_perm[0],
            sport_perm[0],
            hair_perm[0],
            height_perm[0],
            smoothie_perm[0],
            flower_perm[0]
        ],
        [
            "2",
            name_perm[1],
            sport_perm[1],
            hair_perm[1],
            height_perm[1],
            smoothie_perm[1],
            flower_perm[1]
        ]
    ]

    solution_found = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": rows
        }
    }

    # Break early since we found a solution
    break

# Output the solution as JSON
print(json.dumps(solution_found, indent=2))