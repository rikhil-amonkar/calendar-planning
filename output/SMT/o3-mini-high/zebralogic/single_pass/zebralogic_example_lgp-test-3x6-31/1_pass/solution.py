from z3 import *
import json

# We have three houses numbered 1 to 3 from left (index 0) to right (index 2).
# For each house we assign the following attributes:
# Name:   (0: Eric, 1: Peter, 2: Arnold)
# Drink:  (0: milk, 1: water, 2: tea)
# Vacation: (0: mountain, 1: city, 2: beach)
# HouseStyle: (0: colonial, 1: victorian, 2: ranch)
# Animal: (0: cat, 1: bird, 2: horse)
# Birthday: (0: jan, 1: sept, 2: april)

# Create Z3 integer variables for each attribute in each house (houses indices: 0, 1, 2)
num_houses = 3
names = [Int(f"name_{i}") for i in range(num_houses)]
drinks = [Int(f"drink_{i}") for i in range(num_houses)]
vacations = [Int(f"vacation_{i}") for i in range(num_houses)]
styles = [Int(f"style_{i}") for i in range(num_houses)]
animals = [Int(f"animal_{i}") for i in range(num_houses)]
birthdays = [Int(f"birthday_{i}") for i in range(num_houses)]

solver = Solver()

# Domain constraints: each variable is in the set {0,1,2}
all_vars = names + drinks + vacations + styles + animals + birthdays
for var in all_vars:
    solver.add(var >= 0, var < 3)

# All houses have distinct values for each attribute
solver.add(Distinct(names))
solver.add(Distinct(drinks))
solver.add(Distinct(vacations))
solver.add(Distinct(styles))
solver.add(Distinct(animals))
solver.add(Distinct(birthdays))

# Clue 1:
# "The person living in a colonial-style house is somewhere to the left of the person who likes milk."
# That is, the house with style==colonial (0) appears to the left of the house with drink==milk (0).
for i in range(num_houses):
    for j in range(num_houses):
        # if house i is colonial and house j drinks milk, then i must be strictly less than j.
        solver.add(Implies(And(styles[i] == 0, drinks[j] == 0), i < j))

# Clue 2:
# "The person who prefers city breaks is directly left of the person residing in a Victorian house."
# vacation city is 1 and victorian style is 1.
solver.add(Or([And(vacations[i] == 1, styles[i+1] == 1) for i in range(num_houses - 1)]))

# Clue 3:
# "The person whose birthday is in January is directly left of the cat lover."
# Birthday January is 0; cat is animal 0.
solver.add(Or([And(birthdays[i] == 0, animals[i+1] == 0) for i in range(num_houses - 1)]))

# Clue 4:
# "The one who only drinks water is the person who enjoys mountain retreats."
# water is drink 1; mountain is vacation 0.
for i in range(num_houses):
    solver.add(Implies(drinks[i] == 1, vacations[i] == 0))
    solver.add(Implies(vacations[i] == 0, drinks[i] == 1))

# Clue 5:
# "The person who keeps horses is Peter."
# horses is animal 2; Peter is name 1.
for i in range(num_houses):
    solver.add(Implies(animals[i] == 2, names[i] == 1))
    solver.add(Implies(names[i] == 1, animals[i] == 2))

# Clue 6:
# "The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations."
# Victorian is style 1; beach is vacation 2.
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(vacations[i] == 2, styles[j] == 1), i < j))

# Clue 7:
# "Peter is the person who prefers city breaks."
# So, if name is Peter (1) then vacation is city (1); and vice versa.
for i in range(num_houses):
    solver.add(Implies(names[i] == 1, vacations[i] == 1))
    solver.add(Implies(vacations[i] == 1, names[i] == 1))

# Clue 8:
# "The person who enjoys mountain retreats is the person whose birthday is in April."
# mountain is vacation 0; april is birthday 2.
for i in range(num_houses):
    solver.add(Implies(vacations[i] == 0, birthdays[i] == 2))
    solver.add(Implies(birthdays[i] == 2, vacations[i] == 0))

# Clue 9:
# "Eric is the one who only drinks water."
# Eric is name 0; water is drink 1.
for i in range(num_houses):
    solver.add(Implies(names[i] == 0, drinks[i] == 1))
    solver.add(Implies(drinks[i] == 1, names[i] == 0))

# Check and extract solution
if solver.check() == sat:
    model = solver.model()

    # Define mapping dictionaries for each attribute:
    name_map = {0: "Eric", 1: "Peter", 2: "Arnold"}
    drink_map = {0: "milk", 1: "water", 2: "tea"}
    vac_map   = {0: "mountain", 1: "city", 2: "beach"}
    style_map = {0: "colonial", 1: "victorian", 2: "ranch"}
    animal_map = {0: "cat", 1: "bird", 2: "horse"}
    bday_map = {0: "jan", 1: "sept", 2: "april"}

    # Gather the solution for each house (house numbers 1,2,3 corresponding to indices 0,1,2)
    solution_rows = []
    for i in range(num_houses):
        house_num = str(i + 1)
        sol_name = name_map[model[names[i]].as_long()]
        sol_drink = drink_map[model[drinks[i]].as_long()]
        sol_vac = vac_map[model[vacations[i]].as_long()]
        sol_style = style_map[model[styles[i]].as_long()]
        sol_animal = animal_map[model[animals[i]].as_long()]
        sol_bday = bday_map[model[birthdays[i]].as_long()]
        solution_rows.append([house_num, sol_name, sol_drink, sol_vac, sol_style, sol_animal, sol_bday])

    # Prepare final JSON output
    output = {
      "solution": {
         "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
         "rows": solution_rows
      }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")