from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic
names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
animals = ['dog', 'horse', 'cat', 'bird', 'fish']

# Create dictionaries to map each characteristic to an integer variable
name_vars = {name: Int(f'name_{name}') for name in names}
flower_vars = {flower: Int(f'flower_{flower}') for flower in flowers}
animal_vars = {animal: Int(f'animal_{animal}') for animal in animals}

# Add constraints that each variable is between 1 and 5 (inclusive)
for var in list(name_vars.values()) + list(flower_vars.values()) + list(animal_vars.values()):
    solver.add(And(var >= 1, var <= 5))

# Add constraints that each characteristic is unique
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(flower_vars.values())))
solver.add(Distinct(list(animal_vars.values())))

# Apply the given clues
# Clue 1: Alice is in the second house.
solver.add(name_vars['Alice'] == 2)

# Clue 2: The person who loves the boquet of lilies is the bird keeper.
solver.add(flower_vars['lilies'] == animal_vars['bird'])

# Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips.
solver.add(name_vars['Peter'] > flower_vars['tulips'])

# Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils.
solver.add(animal_vars['fish'] == flower_vars['daffodils'])

# Clue 5: The person who keeps horses is Eric.
solver.add(animal_vars['horse'] == name_vars['Eric'])

# Clue 6: There are two houses between the dog owner and Bob.
solver.add(Abs(name_vars['Bob'] - animal_vars['dog']) == 3)

# Clue 7: The fish enthusiast is directly left of Bob.
solver.add(animal_vars['fish'] + 1 == name_vars['Bob'])

# Clue 8: Alice is directly left of the person who keeps horses.
solver.add(name_vars['Alice'] + 1 == animal_vars['horse'])

# Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
solver.add(flower_vars['carnations'] + 1 == flower_vars['tulips'])

# Clue 10: The cat lover is not in the first house.
solver.add(animal_vars['cat'] != 1)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    
    # Create a mapping from house number to characteristics
    house_to_char = {i+1: {'Name': None, 'Flower': None, 'Animal': None} for i in range(5)}
    
    for name, var in name_vars.items():
        house_number = model.evaluate(var).as_long()
        house_to_char[house_number]['Name'] = name
    
    for flower, var in flower_vars.items():
        house_number = model.evaluate(var).as_long()
        house_to_char[house_number]['Flower'] = flower
    
    for animal, var in animal_vars.items():
        house_number = model.evaluate(var).as_long()
        house_to_char[house_number]['Animal'] = animal
    
    # Prepare the solution in the required format
    solution_rows = [[str(house), char['Name'], char['Flower'], char['Animal']] for house, char in house_to_char.items()]
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": solution_rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")