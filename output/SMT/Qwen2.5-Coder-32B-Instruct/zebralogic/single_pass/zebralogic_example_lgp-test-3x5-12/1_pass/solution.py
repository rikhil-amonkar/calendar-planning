from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute
names = ['Eric', 'Peter', 'Arnold']
cigars = ['blue master', 'prince', 'pall mall']
hobbies = ['photography', 'gardening', 'cooking']
educations = ['high school', 'associate', 'bachelor']
drinks = ['tea', 'milk', 'water']

# Create variables for each house
house1_name = String('house1_name')
house2_name = String('house2_name')
house3_name = String('house3_name')

house1_cigar = String('house1_cigar')
house2_cigar = String('house2_cigar')
house3_cigar = String('house3_cigar')

house1_hobby = String('house1_hobby')
house2_hobby = String('house2_hobby')
house3_hobby = String('house3_hobby')

house1_education = String('house1_education')
house2_education = String('house2_education')
house3_education = String('house3_education')

house1_drink = String('house1_drink')
house2_drink = String('house2_drink')
house3_drink = String('house3_drink')

# Add constraints for unique values within each category
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_cigar, house2_cigar, house3_cigar))
solver.add(Distinct(house1_hobby, house2_hobby, house3_hobby))
solver.add(Distinct(house1_education, house2_education, house3_education))
solver.add(Distinct(house1_drink, house2_drink, house3_drink))

# Add constraints based on clues
# Clue 1: The person partial to Pall Mall is Peter.
solver.add(house1_cigar == 'pall mall' >> house1_name == 'Peter')
solver.add(house2_cigar == 'pall mall' >> house2_name == 'Peter')
solver.add(house3_cigar == 'pall mall' >> house3_name == 'Peter')

# Clue 2: The person who likes milk is directly left of the person with a high school diploma.
solver.add(Or(
    And(house1_drink == 'milk', house2_education == 'high school'),
    And(house2_drink == 'milk', house3_education == 'high school')
))

# Clue 3: Eric is the tea drinker.
solver.add(house1_drink == 'tea' >> house1_name == 'Eric')
solver.add(house2_drink == 'tea' >> house2_name == 'Eric')
solver.add(house3_drink == 'tea' >> house3_name == 'Eric')

# Clue 4: Arnold and the Prince smoker are next to each other.
solver.add(Or(
    And(house1_name == 'Arnold', house2_cigar == 'prince'),
    And(house2_name == 'Arnold', house1_cigar == 'prince'),
    And(house2_name == 'Arnold', house3_cigar == 'prince'),
    And(house3_name == 'Arnold', house2_cigar == 'prince')
))

# Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
solver.add(Or(
    And(house1_hobby == 'gardening', Or(house2_cigar == 'prince', house3_cigar == 'prince')),
    And(house2_hobby == 'gardening', house3_cigar == 'prince')
))

# Clue 6: The person who likes milk is the person with an associate's degree.
solver.add(Or(
    And(house1_drink == 'milk', house1_education == 'associate'),
    And(house2_drink == 'milk', house2_education == 'associate'),
    And(house3_drink == 'milk', house3_education == 'associate')
))

# Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
solver.add(Or(
    And(house1_education == 'bachelor', house2_hobby == 'photography'),
    And(house2_education == 'bachelor', house3_hobby == 'photography')
))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": [
                ["1",
                 model[house1_name].as_string(),
                 model[house1_cigar].as_string(),
                 model[house1_hobby].as_string(),
                 model[house1_education].as_string(),
                 model[house1_drink].as_string()],
                ["2",
                 model[house2_name].as_string(),
                 model[house2_cigar].as_string(),
                 model[house2_hobby].as_string(),
                 model[house2_education].as_string(),
                 model[house2_drink].as_string()],
                ["3",
                 model[house3_name].as_string(),
                 model[house3_cigar].as_string(),
                 model[house3_hobby].as_string(),
                 model[house3_education].as_string(),
                 model[house3_drink].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")