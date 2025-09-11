import itertools
import json

# Define all possible options for each category
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']
heights = ['short', 'very short']
educations = ['associate', 'high school']

solution = None

# Iterate through all possible permutations for each category
for hs in itertools.permutations(house_styles):
    if hs[0] != 'victorian':
        continue  # Clue 2: Victorian house is first
    
    for nm in itertools.permutations(names):
        for ht in itertools.permutations(heights):
            # Check Clue 1: Short person is directly left of Eric
            short_pos = ht.index('short')
            if short_pos != 0 or nm[1] != 'Eric':
                continue
                
            for ed in itertools.permutations(educations):
                # Check Clue 3: Short person has associate's degree
                if ed[short_pos] != 'associate':
                    continue
                
                # Build solution if all constraints are satisfied
                rows = [
                    ["1", nm[0], hs[0], ht[0], ed[0]],
                    ["2", nm[1], hs[1], ht[1], ed[1]]
                ]
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                        "rows": rows
                    }
                ]
                # Exit all loops once solution is found
                break
            if solution:
                break
        if solution:
            break
    if solution:
        break

# Output the solution as JSON
print(json.dumps(solution, indent=2))