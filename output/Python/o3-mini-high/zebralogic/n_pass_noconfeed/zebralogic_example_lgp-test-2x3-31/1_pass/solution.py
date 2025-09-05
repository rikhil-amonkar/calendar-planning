import json
import itertools

# Puzzle parameters
houses = [1, 2]
names = ["Eric", "Arnold"]
sports = ["basketball", "soccer"]
hobbies = ["photography", "gardening"]

def satisfies_constraints(name_perm, sport_perm, hobby_perm):
    # Constraint 1: The person who enjoys gardening is Arnold.
    for i in range(len(houses)):
        if hobby_perm[i] == "gardening" and name_perm[i] != "Arnold":
            return False
    # Constraint 2: The photography enthusiast is not in the first house.
    if hobby_perm[0] == "photography":
        return False
    # Constraint 3: The person who loves soccer is not in the first house.
    if sport_perm[0] == "soccer":
        return False
    return True

solution_found = None

# Iterate over all permutations of names, sports, and hobbies for each house
for name_perm in itertools.permutations(names):
    for sport_perm in itertools.permutations(sports):
        for hobby_perm in itertools.permutations(hobbies):
            if satisfies_constraints(name_perm, sport_perm, hobby_perm):
                # Build the solution structure based on the house order (1, 2)
                solution_found = [
                    {"House": "1", "Name": name_perm[0], "FavoriteSport": sport_perm[0], "Hobby": hobby_perm[0]},
                    {"House": "2", "Name": name_perm[1], "FavoriteSport": sport_perm[1], "Hobby": hobby_perm[1]}
                ]
                break
        if solution_found:
            break
    if solution_found:
        break

# Build JSON result in the required format
result = {
    "solution": {
        "header": ["House", "Name", "FavoriteSport", "Hobby"],
        "rows": [
            [house["House"], house["Name"], house["FavoriteSport"], house["Hobby"]]
            for house in solution_found
        ]
    }
}

print(json.dumps(result))