from z3 import *

# Define variables for each attribute of each person in each house
house1_name = String('house1_name')
house1_occupation = String('house1_occupation')
house1_birthday = String('house1_birthday')
house1_housestyle = String('house1_housestyle')
house1_height = String('house1_height')
house1_cigar = String('house1_cigar')

house2_name = String('house2_name')
house2_occupation = String('house2_occupation')
house2_birthday = String('house2_birthday')
house2_housestyle = String('house2_housestyle')
house2_height = String('house2_height')
house2_cigar = String('house2_cigar')

# Create a solver instance
solver = Solver()

# Define the domain of each variable
names = ['Arnold', 'Eric']
occupations = ['engineer', 'doctor']
birthdays = ['april', 'sept']
housestyles = ['victorian', 'colonial']
heights = ['very short', 'short']
cigars = ['pall mall', 'prince']

solver.add(house1_name == Or(*[StringVal(name) for name in names]))
solver.add(house1_occupation == Or(*[StringVal(occupation) for occupation in occupations]))
solver.add(house1_birthday == Or(*[StringVal(birthday) for birthday in birthdays]))
solver.add(house1_housestyle == Or(*[StringVal(housestyle) for housestyle in housestyles]))
solver.add(house1_height == Or(*[StringVal(height) for height in heights]))
solver.add(house1_cigar == Or(*[StringVal(cigar) for cigar in cigars]))

solver.add(house2_name == Or(*[StringVal(name) for name in names]))
solver.add(house2_occupation == Or(*[StringVal(occupation) for occupation in occupations]))
solver.add(house2_birthday == Or(*[StringVal(birthday) for birthday in birthdays]))
solver.add(house2_housestyle == Or(*[StringVal(housestyle) for housestyle in housestyles]))
solver.add(house2_height == Or(*[StringVal(height) for height in heights]))
solver.add(house2_cigar == Or(*[StringVal(cigar) for cigar in cigars]))

# Add constraints based on clues
# Clue 1: The person who is an engineer is in the first house.
solver.add(house1_occupation == 'engineer')

# Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
solver.add(Or(And(house1_birthday == 'april', house2_occupation == 'doctor'), And(house2_birthday == 'april', house1_occupation == 'doctor')))

# Clue 3: The person living in a colonial-style house is the person who is an engineer.
solver.add(house1_housestyle == 'colonial')

# Clue 4: The person who is very short is the person who is an engineer.
solver.add(house1_height == 'very short')

# Clue 5: The person who is short is the person partial to Pall Mall.
solver.add(house2_height == 'short')
solver.add(house2_cigar == 'pall mall')

# Clue 6: The person who is an engineer is Eric.
solver.add(house1_name == 'Eric')

# Ensure all attributes are unique per person and per house
solver.add(Distinct(house1_name, house2_name))
solver.add(Distinct(house1_occupation, house2_occupation))
solver.add(Distinct(house1_birthday, house2_birthday))
solver.add(Distinct(house1_housestyle, house2_housestyle))
solver.add(Distinct(house1_height, house2_height))
solver.add(Distinct(house1_cigar, house2_cigar))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_occupation].as_string(), model[house1_birthday].as_string(), model[house1_housestyle].as_string(), model[house1_height].as_string(), model[house1_cigar].as_string()],
                ["2", model[house2_name].as_string(), model[house2_occupation].as_string(), model[house2_birthday].as_string(), model[house2_housestyle].as_string(), model[house2_height].as_string(), model[house2_cigar].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")