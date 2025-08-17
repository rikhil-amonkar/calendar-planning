import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Arnold']
sports = ['basketball', 'soccer']
hobbies = ['photography', 'gardening']

solution_found = None

# Iterate through all possible permutations
for name_perm in itertools.permutations(names):
    for sport_perm in itertools.permutations(sports):
        for hobby_perm in itertools.permutations(hobbies):
            # Check constraint 1: Arnold has gardening
            gardening_house = hobby_perm.index('gardening')
            if name_perm[gardening_house] != 'Arnold':
                continue
            # Check constraint 2: photography not in first house
            if hobby_perm[0] == 'photography':
                continue
            # Check constraint 3: soccer not in first house
            if sport_perm[0] == 'soccer':
                continue
            # If all constraints are satisfied
            solution_found = (name_perm, sport_perm, hobby_perm)
            break
        if solution_found:
            break
    if solution_found:
        break

# Build the solution structure
rows = []
for i in range(2):
    house_number = str(i + 1)
    name = solution_found[0][i]
    sport = solution_found[1][i]
    hobby = solution_found[2][i]
    rows.append([house_number, name, sport, hobby])

solution_dict = {
    "solution": {
        "header": ["House", "Name", "FavoriteSport", "Hobby"],
        "rows": rows
    }
}

# Output JSON
print(json.dumps(solution_dict, indent=2))