from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute for each house
names = ['Peter', 'Arnold', 'Eric']
car_models = ['toyota camry', 'ford f150', 'tesla model 3']
house_styles = ['ranch', 'colonial', 'victorian']
pets = ['cat', 'dog', 'fish']
occupations = ['engineer', 'doctor', 'teacher']
vacations = ['city', 'mountain', 'beach']

# Create variables for each house
house1_name = String('house1_name')
house1_car_model = String('house1_car_model')
house1_house_style = String('house1_house_style')
house1_pet = String('house1_pet')
house1_occupation = String('house1_occupation')
house1_vacation = String('house1_vacation')

house2_name = String('house2_name')
house2_car_model = String('house2_car_model')
house2_house_style = String('house2_house_style')
house2_pet = String('house2_pet')
house2_occupation = String('house2_occupation')
house2_vacation = String('house2_vacation')

house3_name = String('house3_name')
house3_car_model = String('house3_car_model')
house3_house_style = String('house3_house_style')
house3_pet = String('house3_pet')
house3_occupation = String('house3_occupation')
house3_vacation = String('house3_vacation')

# Add constraints for unique values within each category
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_car_model, house2_car_model, house3_car_model))
solver.add(Distinct(house1_house_style, house2_house_style, house3_house_style))
solver.add(Distinct(house1_pet, house2_pet, house3_pet))
solver.add(Distinct(house1_occupation, house2_occupation, house3_occupation))
solver.add(Distinct(house1_vacation, house2_vacation, house3_vacation))

# Add constraints based on clues
# Clue 1
solver.add(house1_pet == 'fish')

# Clue 2
solver.add(house2_car_model == 'toyota camry')

# Clue 3
solver.add(Or(house1_vacation != 'mountain', house3_vacation != 'mountain'))

# Clue 4
solver.add(Or(house1_vacation != 'city', house3_vacation != 'city'))

# Clue 5
solver.add(Or(house1_name == 'Peter', house2_name == 'Peter'))

# Clue 6
solver.add(house2_house_style == 'colonial')
solver.add(house1_car_model == 'toyota camry')

# Clue 7
solver.add(house1_pet == 'cat' | house2_pet == 'cat' | house3_pet == 'cat')
solver.add(house1_name == 'Arnold' | house2_name == 'Arnold' | house3_name == 'Arnold')
solver.add(If(house1_pet == 'cat', house1_name == 'Arnold', True))
solver.add(If(house2_pet == 'cat', house2_name == 'Arnold', True))
solver.add(If(house3_pet == 'cat', house3_name == 'Arnold', True))

# Clue 8
solver.add(Or((house1_name == 'Eric' & (house2_vacation == 'mountain' | house3_vacation == 'mountain')),
               (house2_name == 'Eric' & house3_vacation == 'mountain')))

# Clue 9
solver.add(Or(house1_occupation != 'engineer', house2_occupation != 'engineer'))

# Clue 10
solver.add(Or((house1_car_model == 'tesla model 3' & (house2_occupation == 'teacher' | house3_occupation == 'teacher')),
               (house2_car_model == 'tesla model 3' & house3_occupation == 'teacher')))

# Clue 11
solver.add(house1_pet == 'dog' | house2_pet == 'dog' | house3_pet == 'dog')
solver.add(house1_occupation == 'engineer' | house2_occupation == 'engineer' | house3_occupation == 'engineer')
solver.add(If(house1_pet == 'dog', house1_occupation == 'engineer', True))
solver.add(If(house2_pet == 'dog', house2_occupation == 'engineer', True))
solver.add(If(house3_pet == 'dog', house3_occupation == 'engineer', True))

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": [
                ["1", m[house1_name].as_string(), m[house1_car_model].as_string(), m[house1_house_style].as_string(),
                 m[house1_pet].as_string(), m[house1_occupation].as_string(), m[house1_vacation].as_string()],
                ["2", m[house2_name].as_string(), m[house2_car_model].as_string(), m[house2_house_style].as_string(),
                 m[house2_pet].as_string(), m[house2_occupation].as_string(), m[house2_vacation].as_string()],
                ["3", m[house3_name].as_string(), m[house3_car_model].as_string(), m[house3_house_style].as_string(),
                 m[house3_pet].as_string(), m[house3_occupation].as_string(), m[house3_vacation].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")