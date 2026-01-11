import itertools
import json

# Define the domains for each attribute
names = ['Eric', 'Arnold']
mothers = ['Aniya', 'Holly']
cars = ['ford f150', 'tesla model 3']
heights = ['short', 'very short']

# Generate all possible combinations for each house
all_combinations = list(itertools.product(names, mothers, cars, heights))

# Initialize possible solutions for each house
house1_possible = []
house2_possible = []

# Apply constraints to filter out invalid combinations
for comb in all_combinations:
    name, mother, car, height = comb
    
    # Check Clue 2: Arnold is the person who is short
    if name == 'Arnold' and height != 'short':
        continue
    if name != 'Arnold' and height == 'short':
        continue
    
    # Check Clue 3: The person whose mother's name is Holly is in the second house
    if mother == 'Holly':
        house2_possible.append(comb)
    else:
        house1_possible.append(comb)

# Further filtering based on Clue 1: Tesla owner is to the right of Arnold
final_solution = None
for h1 in house1_possible:
    for h2 in house2_possible:
        name1, _, car1, _ = h1
        name2, _, car2, _ = h2
        
        # Check Clue 1: Tesla owner is to the right of Arnold
        if name1 == 'Arnold' and car2 == 'tesla model 3':
            final_solution = [h1, h2]
            break
    if final_solution:
        break

# Prepare the output in the required JSON format
if final_solution:
    house1_data = ["1"] + list(final_solution[0])
    house2_data = ["2"] + list(final_solution[1])
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": [house1_data, house2_data]
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")