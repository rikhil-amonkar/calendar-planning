from z3 import *

# Define the houses
houses = [Int(f'house_{i}') for i in range(1, 6)]

# Define the domains for each attribute
names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
heights = ['very short', 'short', 'tall', 'average', 'very tall']
mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']

# Create dictionaries to map attributes to Z3 variables
name_vars = {name: Int(f'name_{name}') for name in names}
height_vars = {height: Int(f'height_{height}') for height in heights}
mother_vars = {mother: Int(f'mother_{mother}') for mother in mothers}
hair_color_vars = {hair_color: Int(f'hair_color_{hair_color}') for hair_color in hair_colors}

# Create a solver instance
solver = Solver()

# Add constraints for unique values for each attribute
solver.add(Distinct(houses))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(height_vars.values()))
solver.add(Distinct(mother_vars.values()))
solver.add(Distinct(hair_color_vars.values()))

# Add constraints for each clue
# 1. The person who is tall is The person whose mother's name is Holly.
solver.add(height_vars['tall'] == mother_vars['Holly'])

# 2. There are two houses between the person who has an average height and the person who is short.
solver.add(Abs(height_vars['average'] - height_vars['short']) == 3)

# 3. The person who has gray hair is directly left of The person whose mother's name is Janelle.
solver.add(hair_color_vars['gray'] + 1 == mother_vars['Janelle'])

# 4. The person who has black hair is not in the fourth house.
solver.add(hair_color_vars['black'] != 4)

# 5. Eric is the person who has black hair.
solver.add(name_vars['Eric'] == hair_color_vars['black'])

# 6. The person who is very short is The person whose mother's name is Penny.
solver.add(height_vars['very short'] == mother_vars['Penny'])

# 7. Eric and the person who has gray hair are next to each other.
solver.add(Abs(name_vars['Eric'] - hair_color_vars['gray']) == 1)

# 8. Bob is in the fifth house.
solver.add(name_vars['Bob'] == 5)

# 9. The person who has red hair is Peter.
solver.add(name_vars['Peter'] == hair_color_vars['red'])

# 10. The person whose mother's name is Kailyn is directly left of the person who is short.
solver.add(mother_vars['Kailyn'] + 1 == height_vars['short'])

# 11. Arnold is the person who has brown hair.
solver.add(name_vars['Arnold'] == hair_color_vars['brown'])

# 12. The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
solver.add(hair_color_vars['brown'] < mother_vars['Janelle'])

# 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
solver.add(Abs(mother_vars['Aniya'] - height_vars['very short']) == 1)

# 14. The person whose mother's name is Kailyn is in the third house.
solver.add(mother_vars['Kailyn'] == 3)

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution = []
    for house in range(1, 6):
        name = next(key for key, value in name_vars.items() if model.evaluate(value) == house)
        height = next(key for key, value in height_vars.items() if model.evaluate(value) == house)
        mother = next(key for key, value in mother_vars.items() if model.evaluate(value) == house)
        hair_color = next(key for key, value in hair_color_vars.items() if model.evaluate(value) == house)
        solution.append([str(house), name, height, mother, hair_color])
    
    # Format the solution as JSON
    import json
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")