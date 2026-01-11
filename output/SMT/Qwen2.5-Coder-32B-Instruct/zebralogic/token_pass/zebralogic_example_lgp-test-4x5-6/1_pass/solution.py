from z3 import *

# Define the domain for each characteristic
names = ['Peter', 'Eric', 'Alice', 'Arnold']
educations = ['bachelor', 'high school', 'associate', 'master']
music_genres = ['jazz', 'rock', 'pop', 'classical']
colors = ['green', 'red', 'yellow', 'white']
flowers = ['lilies', 'carnations', 'daffodils', 'roses']

# Create variables for each house
house_vars = []
for i in range(4):
    house_vars.append({
        'name': Int(f'name_{i+1}'),
        'education': Int(f'education_{i+1}'),
        'music_genre': Int(f'music_genre_{i+1}'),
        'color': Int(f'color_{i+1}'),
        'flower': Int(f'flower_{i+1}')
    })

# Create a solver instance
solver = Solver()

# Add constraints for unique values in each category across houses
for category in ['name', 'education', 'music_genre', 'color', 'flower']:
    solver.add(Distinct([house_vars[i][category] for i in range(4)]))

# Map each value to a unique integer
value_map = {v: i for i, v in enumerate(names + educations + music_genres + colors + flowers)}

# Add constraints based on the clues
# Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
solver.add(house_vars[i]['education'] == value_map['bachelor'] for i in range(4) if house_vars[i]['flower'] == value_map['daffodils'])

# Clue 2: The person who loves a carnations arrangement is not in the first house.
solver.add(house_vars[0]['flower'] != value_map['carnations'])

# Clue 3: The person with a master's degree is Alice.
solver.add(house_vars[i]['education'] == value_map['master'] for i in range(4) if house_vars[i]['name'] == value_map['Alice'])

# Clue 4: The person with a master's degree is directly left of the person who loves classical music.
for i in range(3):
    solver.add(Implies(house_vars[i]['education'] == value_map['master'], house_vars[i+1]['music_genre'] == value_map['classical']))

# Clue 5: Eric is not in the second house.
solver.add(house_vars[1]['name'] != value_map['Eric'])

# Clue 6: Arnold is not in the third house.
solver.add(house_vars[2]['name'] != value_map['Arnold'])

# Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
for i in range(3):
    solver.add(Implies(house_vars[i]['color'] == value_map['yellow'], house_vars[i+1]['flower'] == value_map['roses']))

# Clue 8: The person who loves pop music is in the second house.
solver.add(house_vars[1]['music_genre'] == value_map['pop'])

# Clue 9: The person with an associate's degree is not in the fourth house.
solver.add(house_vars[3]['education'] != value_map['associate'])

# Clue 10: The person who loves a carnations arrangement is not in the fourth house.
solver.add(house_vars[3]['flower'] != value_map['carnations'])

# Clue 11: The person whose favorite color is red is directly left of the person who loves white.
for i in range(3):
    solver.add(Implies(house_vars[i]['color'] == value_map['red'], house_vars[i+1]['color'] == value_map['white']))

# Clue 12: The person whose favorite color is red is the person who loves rock music.
solver.add(house_vars[i]['color'] == value_map['red'] for i in range(4) if house_vars[i]['music_genre'] == value_map['rock'])

# Clue 13: Arnold is the person who loves yellow.
solver.add(house_vars[i]['name'] == value_map['Arnold'] for i in range(4) if house_vars[i]['color'] == value_map['yellow'])

# Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
solver.add(house_vars[i]['flower'] == value_map['daffodils'] for i in range(4) if house_vars[i]['color'] == value_map['yellow'])

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Reverse map to get the original values
    reverse_value_map = {v: k for k, v in value_map.items()}
    
    # Prepare the output
    rows = []
    for i in range(4):
        row = [
            str(i + 1),
            reverse_value_map[model[house_vars[i]['name']].as_long()],
            reverse_value_map[model[house_vars[i]['education']].as_long()],
            reverse_value_map[model[house_vars[i]['music_genre']].as_long()],
            reverse_value_map[model[house_vars[i]['color']].as_long()],
            reverse_value_map[model[house_vars[i]['flower']].as_long()]
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": rows
        }
    }
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")