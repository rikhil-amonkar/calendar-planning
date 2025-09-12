from z3 import *
import json

# Define the variables
houses = [1, 2]
names = ['Eric', 'Arnold']
mothers = ['Aniya', 'Holly']
cars = ['ford f150', 'tesla model 3']
heights = ['short', 'very short']

# Create symbolic variables
name_vars = {house: Int(f'name_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
car_vars = {house: Int(f'car_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([mother_vars[house] for house in houses]))
solver.add(Distinct([car_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))

# Map symbolic variables to actual values
name_map = {i: name for i, name in enumerate(names)}
mother_map = {i: mother for i, mother in enumerate(mothers)}
car_map = {i: car for i, car in enumerate(cars)}
height_map = {i: height for i, height in enumerate(heights)}

# Add constraints based on clues
# Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
solver.add(Or(car_vars[2] == cars.index('tesla model 3'), 
              And(car_vars[1] == cars.index('tesla model 3'), name_vars[2] != names.index('Arnold'))))

# Clue 2: Arnold is the person who is short.
solver.add(name_vars[1] == names.index('Arnold'))
solver.add(height_vars[1] == heights.index('short'))

# Clue 3: The person whose mother's name is Holly is in the second house.
solver.add(mother_vars[2] == mothers.index('Holly'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": []
        }
    }
    for house in houses:
        name = name_map[model[name_vars[house]].as_long()]
        mother = mother_map[model[mother_vars[house]].as_long()]
        car = car_map[model[car_vars[house]].as_long()]
        height = height_map[model[height_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, mother, car, height])
    
    print(json.dumps(solution))
else:
    print("No solution found")