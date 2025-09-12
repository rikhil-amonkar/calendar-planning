from z3 import *

# Define the variables
houses = [1, 2]
names = ['Arnold', 'Eric']
sports = ['basketball', 'soccer']
hair_colors = ['brown', 'black']
heights = ['very short', 'short']
smoothies = ['desert', 'cherry']
flowers = ['daffodils', 'carnations']

# Create dictionaries to hold the variables
name_vars = {h: Int(f'name_{h}') for h in houses}
sport_vars = {h: Int(f'sport_{h}') for h in houses}
hair_color_vars = {h: Int(f'hair_color_{h}') for h in houses}
height_vars = {h: Int(f'height_{h}') for h in houses}
smoothie_vars = {h: Int(f'smoothie_{h}') for h in houses}
flower_vars = {h: Int(f'flower_{h}') for h in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([sport_vars[h] for h in houses]))
solver.add(Distinct([hair_color_vars[h] for h in houses]))
solver.add(Distinct([height_vars[h] for h in houses]))
solver.add(Distinct([smoothie_vars[h] for h in houses]))
solver.add(Distinct([flower_vars[h] for h in houses]))

# Map string values to integers
name_map = {n: i for i, n in enumerate(names)}
sport_map = {s: i for i, s in enumerate(sports)}
hair_color_map = {c: i for i, c in enumerate(hair_colors)}
height_map = {h: i for i, h in enumerate(heights)}
smoothie_map = {s: i for i, s in enumerate(smoothies)}
flower_map = {f: i for i, f in enumerate(flowers)}

# Add constraints based on clues
# Clue 1: The person who loves soccer is not in the second house.
solver.add(sport_vars[2] != sport_map['soccer'])

# Clue 2: The Desert smoothie lover is directly left of the person who is very short.
solver.add(smoothie_vars[1] == smoothie_map['desert'])
solver.add(height_vars[2] == height_map['very short'])

# Clue 3: The person who is very short is the person who has brown hair.
for h in houses:
    solver.add(Implies(height_vars[h] == height_map['very short'], hair_color_vars[h] == hair_color_map['brown']))

# Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
for h in houses:
    solver.add(Implies(smoothie_vars[h] == smoothie_map['desert'], flower_vars[h] == flower_map['carnations']))

# Clue 5: Eric and the person who has brown hair are next to each other.
solver.add(Or(
    And(name_vars[1] == name_map['Eric'], hair_color_vars[2] == hair_color_map['brown']),
    And(name_vars[2] == name_map['Eric'], hair_color_vars[1] == hair_color_map['brown'])
))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": []
        }
    }
    for h in houses:
        name_idx = model[name_vars[h]].as_long()
        sport_idx = model[sport_vars[h]].as_long()
        hair_color_idx = model[hair_color_vars[h]].as_long()
        height_idx = model[height_vars[h]].as_long()
        smoothie_idx = model[smoothie_vars[h]].as_long()
        flower_idx = model[flower_vars[h]].as_long()
        
        # Ensure indices are within valid range
        name = names[name_idx] if 0 <= name_idx < len(names) else "Unknown"
        sport = sports[sport_idx] if 0 <= sport_idx < len(sports) else "Unknown"
        hair_color = hair_colors[hair_color_idx] if 0 <= hair_color_idx < len(hair_colors) else "Unknown"
        height = heights[height_idx] if 0 <= height_idx < len(heights) else "Unknown"
        smoothie = smoothies[smoothie_idx] if 0 <= smoothie_idx < len(smoothies) else "Unknown"
        flower = flowers[flower_idx] if 0 <= flower_idx < len(flowers) else "Unknown"
        
        solution["solution"]["rows"].append([str(h), name, sport, hair_color, height, smoothie, flower])
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")