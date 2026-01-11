from z3 import *

# Define variables for each characteristic
name = ['Eric', 'Arnold']
house_style = ['victorian', 'colonial']
height = ['very short', 'short']
education = ['associate', 'high school']

# Create symbolic variables for each house
house1_name = String('house1_name')
house1_house_style = String('house1_house_style')
house1_height = String('house1_height')
house1_education = String('house1_education')

house2_name = String('house2_name')
house2_house_style = String('house2_house_style')
house2_height = String('house2_height')
house2_education = String('house2_education')

# Create solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: The person who is short is directly left of Eric.
solver.add(house2_name == 'Eric')
solver.add(house1_height == 'short')

# Clue 2: The person residing in a Victorian house is in the first house.
solver.add(house1_house_style == 'victorian')

# Clue 3: The person who is short is the person with an associate's degree.
solver.add(house1_education == 'associate')

# All names must be unique
solver.add(Distinct(house1_name, house2_name))

# All house styles must be unique
solver.add(Distinct(house1_house_style, house2_house_style))

# All heights must be unique
solver.add(Distinct(house1_height, house2_height))

# All educations must be unique
solver.add(Distinct(house1_education, house2_education))

# Assign remaining attributes
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))

solver.add(Or(house1_house_style == 'victorian', house1_house_style == 'colonial'))
solver.add(Or(house2_house_style == 'victorian', house2_house_style == 'colonial'))

solver.add(Or(house1_height == 'very short', house1_height == 'short'))
solver.add(Or(house2_height == 'very short', house2_height == 'short'))

solver.add(Or(house1_education == 'associate', house1_education == 'high school'))
solver.add(Or(house2_education == 'associate', house2_education == 'high school'))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_house_style].as_string(), model[house1_height].as_string(), model[house1_education].as_string()],
                ["2", model[house2_name].as_string(), model[house2_house_style].as_string(), model[house2_height].as_string(), model[house2_education].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")