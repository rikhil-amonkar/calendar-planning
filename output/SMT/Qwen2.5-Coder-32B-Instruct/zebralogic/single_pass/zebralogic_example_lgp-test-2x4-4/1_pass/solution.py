from z3 import *

# Create Solver instance
solver = Solver()

# Define variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_style = String('house1_style')
house2_style = String('house2_style')
house1_height = String('house1_height')
house2_height = String('house2_height')
house1_education = String('house1_education')
house2_education = String('house2_education')

# Define domains
names = ['Eric', 'Arnold']
styles = ['victorian', 'colonial']
heights = ['very short', 'short']
educations = ['associate', 'high school']

# Add constraints for uniqueness
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_style, house2_style))
solver.add(Distinct(house1_height, house2_height))
solver.add(Distinct(house1_education, house2_education))

# Add constraints based on clues
# Clue 1: The person who is short is directly left of Eric.
solver.add(Implies(house2_name == 'Eric', house1_height == 'short'))

# Clue 2: The person residing in a Victorian house is in the first house.
solver.add(house1_style == 'victorian')

# Clue 3: The person who is short is the person with an associate's degree.
solver.add(Implies(house1_height == 'short', house1_education == 'associate'))
solver.add(Implies(house2_height == 'short', house2_education == 'associate'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    house1_solution = [str(model[eval(f'house1_{attr}')]) for attr in ['name', 'style', 'height', 'education']]
    house2_solution = [str(model[eval(f'house2_{attr}')]) for attr in ['name', 'style', 'height', 'education']]
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [
                ["1"] + house1_solution,
                ["2"] + house2_solution
            ]
        }
    }
    print(solution)
else:
    print("No solution found")