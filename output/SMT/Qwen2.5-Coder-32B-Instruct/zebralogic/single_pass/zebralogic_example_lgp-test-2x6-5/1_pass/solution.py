from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Arnold', 'Eric']
occupations = ['engineer', 'doctor']
birthdays = ['april', 'sept']
house_styles = ['victorian', 'colonial']
heights = ['very short', 'short']
cigars = ['pall mall', 'prince']

# Create symbolic variables
house1_name = String('house1_name')
house2_name = String('house2_name')
house1_occupation = String('house1_occupation')
house2_occupation = String('house2_occupation')
house1_birthday = String('house1_birthday')
house2_birthday = String('house2_birthday')
house1_house_style = String('house1_house_style')
house2_house_style = String('house2_house_style')
house1_height = String('house1_height')
house2_height = String('house2_height')
house1_cigar = String('house1_cigar')
house2_cigar = String('house2_cigar')

# Add constraints
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))
solver.add(house1_name != house2_name)

solver.add(Or(house1_occupation == 'engineer', house1_occupation == 'doctor'))
solver.add(Or(house2_occupation == 'engineer', house2_occupation == 'doctor'))
solver.add(house1_occupation != house2_occupation)

solver.add(Or(house1_birthday == 'april', house1_birthday == 'sept'))
solver.add(Or(house2_birthday == 'april', house2_birthday == 'sept'))
solver.add(house1_birthday != house2_birthday)

solver.add(Or(house1_house_style == 'victorian', house1_house_style == 'colonial'))
solver.add(Or(house2_house_style == 'victorian', house2_house_style == 'colonial'))
solver.add(house1_house_style != house2_house_style)

solver.add(Or(house1_height == 'very short', house1_height == 'short'))
solver.add(Or(house2_height == 'very short', house2_height == 'short'))
solver.add(house1_height != house2_height)

solver.add(Or(house1_cigar == 'pall mall', house1_cigar == 'prince'))
solver.add(Or(house2_cigar == 'pall mall', house2_cigar == 'prince'))
solver.add(house1_cigar != house2_cigar)

# Clues
solver.add(house1_occupation == 'engineer')  # Clue 1
solver.add(Implies(house1_birthday == 'april', house2_occupation == 'doctor'))  # Clue 2 part 1
solver.add(Implies(house2_birthday == 'april', house1_occupation == 'doctor'))  # Clue 2 part 2
solver.add(house1_house_style == 'colonial')  # Clue 3
solver.add(house1_height == 'very short')  # Clue 4
solver.add(house2_height == 'short')  # Clue 5
solver.add(house2_cigar == 'pall mall')  # Derived from Clue 5
solver.add(house1_name == 'Eric')  # Clue 6
solver.add(house2_name == 'Arnold')  # Derived from Clue 6

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": [
                ["1",
                 model[house1_name].as_string(),
                 model[house1_occupation].as_string(),
                 model[house1_birthday].as_string(),
                 model[house1_house_style].as_string(),
                 model[house1_height].as_string(),
                 model[house1_cigar].as_string()],
                ["2",
                 model[house2_name].as_string(),
                 model[house2_occupation].as_string(),
                 model[house2_birthday].as_string(),
                 model[house2_house_style].as_string(),
                 model[house2_height].as_string(),
                 model[house2_cigar].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")