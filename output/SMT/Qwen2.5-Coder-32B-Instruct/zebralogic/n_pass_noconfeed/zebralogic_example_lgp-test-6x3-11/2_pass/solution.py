from z3 import *

# Define the variables
names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

# Create a solver instance
solver = Solver()

# Define the variables for each house
house_vars = {}
for i in range(1, 7):
    house_vars[i] = {
        'name': Int(f'name_{i}'),
        'hair_color': Int(f'hair_color_{i}'),
        'height': Int(f'height_{i}')
    }

# Add constraints for unique values in each category
solver.add(Distinct([house_vars[i]['name'] for i in range(1, 7)]))
solver.add(Distinct([house_vars[i]['hair_color'] for i in range(1, 7)]))
solver.add(Distinct([house_vars[i]['height'] for i in range(1, 7)]))

# Map names, hair colors, and heights to integers
name_map = {name: i for i, name in enumerate(names)}
hair_color_map = {color: i for i, color in enumerate(hair_colors)}
height_map = {height: i for i, height in enumerate(heights)}

# Add constraints based on the clues
# Clue 1: The person who has blonde hair is directly left of Bob.
solver.add(house_vars[1]['hair_color'] == hair_color_map['blonde'])
solver.add(house_vars[2]['name'] == name_map['Bob'])

# Clue 2: Alice is in the fourth house.
solver.add(house_vars[4]['name'] == name_map['Alice'])

# Clue 3: The person who is short is Arnold.
for i in range(1, 7):
    solver.add(Implies(house_vars[i]['name'] == name_map['Arnold'], house_vars[i]['height'] == height_map['short']))

# Clue 4: The person who is tall is in the sixth house.
solver.add(house_vars[6]['height'] == height_map['tall'])

# Clue 5: The person who has black hair is not in the fourth house.
solver.add(house_vars[4]['hair_color'] != hair_color_map['black'])

# Clue 6: The person who has red hair is Eric.
for i in range(1, 7):
    solver.add(Implies(house_vars[i]['name'] == name_map['Eric'], house_vars[i]['hair_color'] == hair_color_map['red']))

# Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
solver.add(Or([And(house_vars[i]['height'] == height_map['average'], house_vars[j]['height'] == height_map['super tall']) for i in range(1, 6) for j in range(i+1, 7)]))

# Clue 8: The person who has blonde hair is Carol.
for i in range(1, 7):
    solver.add(Implies(house_vars[i]['name'] == name_map['Carol'], house_vars[i]['hair_color'] == hair_color_map['blonde']))

# Clue 9: There is one house between the person who has gray hair and the person who has red hair.
solver.add(Or([And(house_vars[i]['hair_color'] == hair_color_map['gray'], house_vars[i+2]['hair_color'] == hair_color_map['red']) for i in range(1, 5)] +
              [And(house_vars[i]['hair_color'] == hair_color_map['red'], house_vars[i+2]['hair_color'] == hair_color_map['gray']) for i in range(1, 5)]))

# Clue 10: The person who is very short is in the fifth house.
solver.add(house_vars[5]['height'] == height_map['very short'])

# Clue 11: Bob is the person who has brown hair.
for i in range(1, 7):
    solver.add(Implies(house_vars[i]['name'] == name_map['Bob'], house_vars[i]['hair_color'] == hair_color_map['brown']))

# Clue 12: The person who has gray hair is in the third house.
solver.add(house_vars[3]['hair_color'] == hair_color_map['gray'])

# Clue 13: The person who has blonde hair is the person who is very tall.
for i in range(1, 7):
    solver.add(Implies(house_vars[i]['hair_color'] == hair_color_map['blonde'], house_vars[i]['height'] == height_map['very tall']))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }
    for i in range(1, 7):
        name = names[model.eval(house_vars[i]['name']).as_long()]
        hair_color = hair_colors[model.eval(house_vars[i]['hair_color']).as_long()]
        height = heights[model.eval(house_vars[i]['height']).as_long()]
        solution["solution"]["rows"].append([str(i), name, hair_color, height])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")