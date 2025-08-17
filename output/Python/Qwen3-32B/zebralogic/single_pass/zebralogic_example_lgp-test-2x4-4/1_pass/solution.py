import itertools
import json

# Define possible values for each attribute
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']
heights = ['very short', 'short']
education = ['associate', 'high school']

# Generate all permutations for each attribute
name_perms = list(itertools.permutations(names))
style_perms = list(itertools.permutations(house_styles))
height_perms = list(itertools.permutations(heights))
education_perms = list(itertools.permutations(education))

solution = None

# Check all combinations of permutations
for n in name_perms:
    for s in style_perms:
        for h in height_perms:
            for e in education_perms:
                # Clue 2: Victorian house is first
                if s[0] != 'victorian':
                    continue
                # Clue 1: Short person is directly left of Eric
                if h[0] == 'short' and n[1] == 'Eric':
                    # Clue 3: Short person has associate degree
                    if e[0] == 'associate':
                        # Construct solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                                "rows": [
                                    ["1", n[0], s[0], h[0], e[0]],
                                    ["2", n[1], s[1], h[1], e[1]]
                                ]
                            }
                        }
                        # Exit loops once solution is found
                        break
            else:
                continue
            break
        if solution:
            break
    if solution:
        break

# Output solution as JSON
print(json.dumps(solution))