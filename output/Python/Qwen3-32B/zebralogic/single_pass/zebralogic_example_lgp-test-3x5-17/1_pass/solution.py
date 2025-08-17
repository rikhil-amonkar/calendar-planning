import itertools
import json

# Define all possible values for each category
names = ['Eric', 'Arnold', 'Peter']
phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
heights = ['very short', 'average', 'short']
cars = ['tesla model 3', 'toyota camry', 'ford f150']
house_styles = ['ranch', 'colonial', 'victorian']  # Fixed by clues 2 and 6

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
phone_perms = list(itertools.permutations(phones))
height_perms = list(itertools.permutations(heights))
car_perms = list(itertools.permutations(cars))

solution = None

# Iterate through all possible combinations
for n in name_perms:
    for p in phone_perms:
        for h in height_perms:
            for c in car_perms:
                # Check constraint 7: Arnold is in the second house
                if n[1] != 'Arnold':
                    continue
                
                # Check constraint 9: Average height in the first house
                if h[0] != 'average':
                    continue
                
                # Check constraint 1: Peter is to the right of Eric
                eric_idx = n.index('Eric')
                peter_idx = n.index('Peter')
                if eric_idx >= peter_idx:
                    continue
                
                # Check constraint 3: Tesla owner is very short
                tesla_owner = c.index('tesla model 3')
                if h[tesla_owner] != 'very short':
                    continue
                
                # Check constraint 4: Short person directly left of Samsung user
                short_idx = h.index('short')
                if short_idx + 1 >= 3 or p[short_idx + 1] != 'samsung galaxy s21':
                    continue
                
                # Check constraint 5: iPhone directly left of Google Pixel
                iphone_idx = p.index('iphone 13')
                if iphone_idx + 1 >= 3 or p[iphone_idx + 1] != 'google pixel 6':
                    continue
                
                # Check constraint 8: Ford is to the right of Toyota
                toyota_idx = c.index('toyota camry')
                ford_idx = c.index('ford f150')
                if ford_idx <= toyota_idx:
                    continue
                
                # If we reach here, all constraints are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                        "rows": [
                            [str(i+1), n[i], p[i], h[i], house_styles[i], c[i]] for i in range(3)
                        ]
                    }
                }
                # Break out of all loops once a solution is found
                break
            if solution:
                break
        if solution:
            break
    if solution:
        break

# Output the solution in JSON format
print(json.dumps(solution, indent=2))