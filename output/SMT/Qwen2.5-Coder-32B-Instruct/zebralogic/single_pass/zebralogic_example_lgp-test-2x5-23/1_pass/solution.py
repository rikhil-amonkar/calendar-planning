from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic for both houses
names = ['Arnold', 'Eric']
educations = ['associate', 'high school']
heights = ['short', 'very short']
foods = ['grilled cheese', 'pizza']
drinks = ['tea', 'water']

# Declare variables
name1, name2 = Ints('name1 name2')
education1, education2 = Ints('education1 education2')
height1, height2 = Ints('height1 height2')
food1, food2 = Ints('food1 food2')
drink1, drink2 = Ints('drink1 drink2')

# Map strings to integers
name_map = {n: i for i, n in enumerate(names)}
education_map = {e: i for i, e in enumerate(educations)}
height_map = {h: i for i, h in enumerate(heights)}
food_map = {f: i for i, f in enumerate(foods)}
drink_map = {d: i for i, d in enumerate(drinks)}

# Constraints for uniqueness within each category
solver.add(Distinct(name1, name2))
solver.add(Distinct(education1, education2))
solver.add(Distinct(height1, height2))
solver.add(Distinct(food1, food2))
solver.add(Distinct(drink1, drink2))

# Clue constraints
# Clue 1: The person who is very short is the person who is a pizza lover.
solver.add(Implies(height1 == height_map['very short'], food1 == food_map['pizza']))
solver.add(Implies(height2 == height_map['very short'], food2 == food_map['pizza']))

# Clue 2: The person who loves eating grilled cheese is in the second house.
solver.add(food2 == food_map['grilled cheese'])

# Clue 3: The person with a high school diploma is the person who is a pizza lover.
solver.add(Implies(education1 == education_map['high school'], food1 == food_map['pizza']))
solver.add(Implies(education2 == education_map['high school'], food2 == food_map['pizza']))

# Clue 4: The tea drinker is the person who loves eating grilled cheese.
solver.add(Implies(drink1 == drink_map['tea'], food1 == food_map['grilled cheese']))
solver.add(Implies(drink2 == drink_map['tea'], food2 == food_map['grilled cheese']))

# Clue 5: Arnold is the person who is a pizza lover.
solver.add(Implies(name1 == name_map['Arnold'], food1 == food_map['pizza']))
solver.add(Implies(name2 == name_map['Arnold'], food2 == food_map['pizza']))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": [
                ["1", names[model[name1].as_long()], educations[model[education1].as_long()], heights[model[height1].as_long()], foods[model[food1].as_long()], drinks[model[drink1].as_long()]],
                ["2", names[model[name2].as_long()], educations[model[education2].as_long()], heights[model[height2].as_long()], foods[model[food2].as_long()], drinks[model[drink2].as_long()]]
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")