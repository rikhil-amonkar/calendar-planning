from z3 import *

# Create Solver instance
solver = Solver()

# Define variables for each attribute of each person
house1_name = String('house1_name')
house1_mother = String('house1_mother')
house1_car_model = String('house1_car_model')
house1_height = String('house1_height')

house2_name = String('house2_name')
house2_mother = String('house2_mother')
house2_car_model = String('house2_car_model')
house2_height = String('house2_height')

# Define possible values for each attribute
names = ['Eric', 'Arnold']
mothers = ['Aniya', 'Holly']
car_models = ['ford f150', 'tesla model 3']
heights = ['short', 'very short']

# Add constraints for unique values within each attribute across houses
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_mother, house2_mother))
solver.add(Distinct(house1_car_model, house2_car_model))
solver.add(Distinct(house1_height, house2_height))

# Add constraints based on clues
# Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
solver.add(Implies(house2_car_model == 'tesla model 3', house1_name != 'Arnold'))
solver.add(Implies(house1_car_model == 'tesla model 3', False))  # Tesla owner cannot be in house 1

# Clue 2: Arnold is the person who is short.
solver.add(house1_name == 'Arnold' >> house1_height == 'short')
solver.add(house2_name == 'Arnold' >> house2_height == 'short')

# Clue 3: The person whose mother's name is Holly is in the second house.
solver.add(house2_mother == 'Holly')

# Possible values for each variable
solver.add(Or(house1_name == 'Eric', house1_name == 'Arnold'))
solver.add(Or(house1_mother == 'Aniya', house1_mother == 'Holly'))
solver.add(Or(house1_car_model == 'ford f150', house1_car_model == 'tesla model 3'))
solver.add(Or(house1_height == 'short', house1_height == 'very short'))

solver.add(Or(house2_name == 'Eric', house2_name == 'Arnold'))
solver.add(Or(house2_mother == 'Aniya', house2_mother == 'Holly'))
solver.add(Or(house2_car_model == 'ford f150', house2_car_model == 'tesla model 3'))
solver.add(Or(house2_height == 'short', house2_height == 'very short'))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "CarModel", "Height"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_mother].as_string(), model[house1_car_model].as_string(), model[house1_height].as_string()],
                ["2", model[house2_name].as_string(), model[house2_mother].as_string(), model[house2_car_model].as_string(), model[house2_height].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")