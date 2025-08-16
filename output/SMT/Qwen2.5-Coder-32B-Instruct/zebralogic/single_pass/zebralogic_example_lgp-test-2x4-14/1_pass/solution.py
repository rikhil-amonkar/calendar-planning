from z3 import *

# Create Solver instance
solver = Solver()

# Define variables for each characteristic
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']
smoothies = ['cherry', 'desert']
pets = ['dog', 'cat']
houses = [1, 2]

# Declare variables
name_vars = {h: Int(f'name_{h}') for h in houses}
house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
smoothie_vars = {h: Int(f'smoothie_{h}') for h in houses}
pet_vars = {h: Int(f'pet_{h}') for h in houses}

# Map values to integers for constraints
name_map = {n: i for i, n in enumerate(names)}
house_style_map = {hs: i for i, hs in enumerate(house_styles)}
smoothie_map = {s: i for i, s in enumerate(smoothies)}
pet_map = {p: i for i, p in enumerate(pets)}

# Add constraints for unique values per house
for h in houses:
    solver.add(name_vars[h] >= 0)
    solver.add(name_vars[h] < len(names))
    solver.add(house_style_vars[h] >= 0)
    solver.add(house_style_vars[h] < len(house_styles))
    solver.add(smoothie_vars[h] >= 0)
    solver.add(smoothie_vars[h] < len(smoothies))
    solver.add(pet_vars[h] >= 0)
    solver.add(pet_vars[h] < len(pets))

# Ensure all values are unique across houses
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([house_style_vars[h] for h in houses]))
solver.add(Distinct([smoothie_vars[h] for h in houses]))
solver.add(Distinct([pet_vars[h] for h in houses]))

# Add specific clues as constraints
# Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
solver.add(Implies(smoothie_vars[1] == smoothie_map['cherry'], pet_vars[1] == pet_map['dog']))
solver.add(Implies(smoothie_vars[2] == smoothie_map['cherry'], pet_vars[2] == pet_map['dog']))

# Clue 2: The person residing in a Victorian house is the person who owns a dog.
solver.add(Implies(house_style_vars[1] == house_style_map['victorian'], pet_vars[1] == pet_map['dog']))
solver.add(Implies(house_style_vars[2] == house_style_map['victorian'], pet_vars[2] == pet_map['dog']))

# Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
solver.add(Implies(house_style_vars[1] == house_style_map['victorian'], name_vars[1] != name_map['Eric']))
solver.add(Implies(house_style_vars[2] == house_style_map['victorian'], name_vars[1] == name_map['Eric']))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": []
        }
    }
    
    for h in houses:
        name = names[model.evaluate(name_vars[h]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[h]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[h]).as_long()]
        pet = pets[model.evaluate(pet_vars[h]).as_long()]
        
        solution["solution"]["rows"].append([str(h), name, house_style, smoothie, pet])
    
    print(json.dumps(solution, indent=4))
else:
    print("No solution found")