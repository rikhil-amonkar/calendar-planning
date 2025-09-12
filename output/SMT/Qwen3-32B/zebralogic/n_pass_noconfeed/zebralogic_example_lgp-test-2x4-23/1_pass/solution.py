import json
from z3 import *

# Create EnumSorts for each attribute
Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
Mother, (Aniya, Holly) = EnumSort('Mother', ['Aniya', 'Holly'])
Car, (FordF150, TeslaModel3) = EnumSort('Car', ['ford f150', 'tesla model 3'])
Height, (Short, VeryShort) = EnumSort('Height', ['short', 'very short'])

# Create Z3 solver instance
solver = Solver()

# House 1 variables
name1 = Const('name1', Name)
mother1 = Const('mother1', Mother)
car1 = Const('car1', Car)
height1 = Const('height1', Height)

# House 2 variables
name2 = Const('name2', Name)
mother2 = Const('mother2', Mother)
car2 = Const('car2', Car)
height2 = Const('height2', Height)

# Add uniqueness constraints for each attribute
solver.add(name1 != name2)
solver.add(mother1 != mother2)
solver.add(car1 != car2)
solver.add(height1 != height2)

# Add puzzle constraints
# Clue 2: Arnold is short
solver.add(If(name1 == Arnold, height1 == Short, True))
solver.add(If(name2 == Arnold, height2 == Short, True))

# Clue 3: The person with mother Holly is in house 2
solver.add(mother2 == Holly)

# Clue 1: The Tesla owner is to the right of Arnold
solver.add(name1 == Arnold)
solver.add(car2 == TeslaModel3)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    
    # Create mappings from Z3 enum constants to string values
    name_map = {Eric: 'Eric', Arnold: 'Arnold'}
    mother_map = {Aniya: 'Aniya', Holly: 'Holly'}
    car_map = {FordF150: 'ford f150', TeslaModel3: 'tesla model 3'}
    height_map = {Short: 'short', VeryShort: 'very short'}
    
    # Extract values for house 1
    h1_name = name_map[model[name1]]
    h1_mother = mother_map[model[mother1]]
    h1_car = car_map[model[car1]]
    h1_height = height_map[model[height1]]
    
    # Extract values for house 2
    h2_name = name_map[model[name2]]
    h2_mother = mother_map[model[mother2]]
    h2_car = car_map[model[car2]]
    h2_height = height_map[model[height2]]
    
    # Construct the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": [
                ["1", h1_name, h1_mother, h1_car, h1_height],
                ["2", h2_name, h2_mother, h2_car, h2_height]
            ]
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")