import itertools
import json

# Define the categories and their options
categories = [
    ('Name', ['Arnold', 'Eric']),
    ('Occupation', ['engineer', 'doctor']),
    ('Birthday', ['april', 'sept']),
    ('HouseStyle', ['victorian', 'colonial']),
    ('Height', ['very short', 'short']),
    ('Cigar', ['pall mall', 'prince']),
]

# Generate all permutations for each category
permutations_list = []
for cat_name, options in categories:
    perms = list(itertools.permutations(options))
    permutations_list.append(perms)

# Now, generate the product of all permutations across categories
all_perms = permutations_list  # Each entry is the permutations for a category

# Iterate through all possible combinations of permutations
for combination in itertools.product(*all_perms):
    # combination[0] is Name permutation (house1_name, house2_name)
    # combination[1] is Occupation permutation
    # combination[2] is Birthday permutation
    # combination[3] is HouseStyle permutation
    # combination[4] is Height permutation
    # combination[5] is Cigar permutation

    # Check clue 1: engineer is in first house
    if combination[1][0] != 'engineer':
        continue

    # Check clue 6: engineer is Eric → house1's name is Eric
    if combination[0][0] != 'Eric':
        continue

    # Check clue 3: colonial is the engineer's house → house1's HouseStyle is colonial
    if combination[3][0] != 'colonial':
        continue

    # Check clue 4: engineer's height is very short → house1's height is very short
    if combination[4][0] != 'very short':
        continue

    # Check clue 5: short (house2's height) is Pall Mall → house2's cigar is 'pall mall'
    if combination[5][1] != 'pall mall':
        continue

    # Check clue 2: April and doctor are next to each other.
    # Doctor is in house2 (since occupation_perm[1] is 'doctor')
    # So April must be in house1
    if combination[2][0] != 'april':
        continue

    # If all constraints are satisfied, build the solution.
    rows = []
    # house 1
    rows.append([
        "1",
        combination[0][0],  # Name
        combination[1][0],  # Occupation
        combination[2][0],  # Birthday
        combination[3][0],  # HouseStyle
        combination[4][0],  # Height
        combination[5][0],  # Cigar
    ])
    # house 2
    rows.append([
        "2",
        combination[0][1],  # Name
        combination[1][1],  # Occupation
        combination[2][1],  # Birthday
        combination[3][1],  # HouseStyle
        combination[4][1],  # Height
        combination[5][1],  # Cigar
    ])

    # Now create the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": rows
        }
    }

    # Output as JSON
    print(json.dumps(solution))
    break  # Assuming only one solution exists