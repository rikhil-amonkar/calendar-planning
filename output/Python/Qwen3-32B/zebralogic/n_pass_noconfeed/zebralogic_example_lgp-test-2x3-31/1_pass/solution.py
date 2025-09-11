import itertools
import json

# Define possible values for each category
names = ['Eric', 'Arnold']
sports = ['basketball', 'soccer']
hobbies = ['photography', 'gardening']

solution = None

# Iterate through all possible permutations of the categories
for name_perm in itertools.permutations(names):
    for sport_perm in itertools.permutations(sports):
        for hobby_perm in itertools.permutations(hobbies):
            # Check constraint 1: Arnold's hobby is gardening
            valid = True
            for i in range(2):
                if name_perm[i] == 'Arnold' and hobby_perm[i] != 'gardening':
                    valid = False
                    break
            if not valid:
                continue
            
            # Check constraint 2: Photography enthusiast is not in the first house
            for i in range(2):
                if hobby_perm[i] == 'photography' and (i + 1) == 1:
                    valid = False
                    break
            if not valid:
                continue
            
            # Check constraint 3: Soccer lover is not in the first house
            for i in range(2):
                if sport_perm[i] == 'soccer' and (i + 1) == 1:
                    valid = False
                    break
            if not valid:
                continue
            
            # Build the solution if all constraints are satisfied
            rows = []
            for i in range(2):
                house_num = str(i + 1)
                name = name_perm[i]
                sport = sport_perm[i]
                hobby = hobby_perm[i]
                rows.append([house_num, name, sport, hobby])
            solution = rows
            break
        if solution:
            break
    if solution:
        break

# Format the solution into the required JSON structure
json_output = {
    "solution": {
        "header": ["House", "Name", "FavoriteSport", "Hobby"],
        "rows": solution
    }
}

# Print the JSON output
print(json.dumps(json_output, indent=2))