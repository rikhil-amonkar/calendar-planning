import itertools
import json

# Define possible values
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']

solution = None

# Generate all permutations for house styles and names
for hs in itertools.permutations(house_styles):
    for nm in itertools.permutations(names):
        # Check Clue 1: Victorian is left of Colonial
        if hs.index('victorian') < hs.index('colonial'):
            # Check Clue 2: Eric is in the first house
            if nm[0] == 'Eric':
                # Build solution structure
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle"],
                        "rows": [
                            ["1", nm[0], hs[0]],
                            ["2", nm[1], hs[1]]
                        ]
                    }
                }
                break
    if solution:
        break

# Output as JSON
print(json.dumps(solution))