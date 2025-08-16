import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define variables for each house (0-based index for houses 1-6)
names = [z3.Int(f'Name_{i}') for i in range(6)]
house_styles = [z3.Int(f'HouseStyle_{i}') for i in range(6)]
foods = [z3.Int(f'Food_{i}') for i in range(6)]
vacations = [z3.Int(f'Vacation_{i}') for i in range(6)]
heights = [z3.Int(f'Height_{i}') for i in range(6)]
cigars = [z3.Int(f'Cigar_{i}') for i in range(6)]

# All attributes must be distinct and within [0, 5]
for attr in [names, house_styles, foods, vacations, heights, cigars]:
    solver.add(z3.Distinct(attr))
    for v in attr:
        solver.add(v >= 0, v <= 5)

# Clue 1: Alice is in the fifth house (index 4)
solver.add(names[4] == 5)

# Clue 2: stir fry (4) in colonial (1)
for i in range(6):
    solver.add(z3.Implies(foods[i] == 4, house_styles[i] == 1))

# Clue 3: Alice's food is spaghetti (2)
solver.add(foods[4] == 2)

# Clue 4: Arnold (0) loves stew (1)
for i in range(6):
    solver.add(z3.Implies(names[i] == 0, foods[i] == 1))

# Clue 5: avg height (0) and Peter (2) have one house between
avg_height_house = z3.Int('avg_height_house')
peter_house = z3.Int('peter_house')
solver.add(z3.Or(*[z3.And(heights[i] == 0, avg_height_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(names[i] == 2, peter_house == i) for i in range(6)]))
solver.add(z3.Abs(avg_height_house - peter_house) == 2)

# Clue 6: Craftsman (3) not in third house (index 2)
solver.add(house_styles[2] != 3)

# Clue 7: avg height (0) loves stir fry (4)
for i in range(6):
    solver.add(z3.Implies(heights[i] == 0, foods[i] == 4))

# Clue 8: beach (5) in ranch (0)
for i in range(6):
    solver.add(z3.Implies(vacations[i] == 5, house_styles[i] == 0))

# Clue 9: Eric in fourth house (index 3)
solver.add(names[3] == 3)

# Clue 10: colonial (1) and camping (3) have one house between
colonial_house = z3.Int('colonial_house')
camping_house = z3.Int('camping_house')
solver.add(z3.Or(*[z3.And(house_styles[i] == 1, colonial_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(vacations[i] == 3, camping_house == i) for i in range(6)]))
solver.add(z3.Abs(colonial_house - camping_house) == 2)

# Clue 11: mountain (2) smoker is yellow monster (0)
for i in range(6):
    solver.add(z3.Implies(vacations[i] == 2, cigars[i] == 0))

# Clue 12: mountain (2) is very tall (1)
for i in range(6):
    solver.add(z3.Implies(vacations[i] == 2, heights[i] == 1))

# Clue 13: mountain and Dunhill (2) are next to each other
mountain_house = z3.Int('mountain_house')
dunhill_house = z3.Int('dunhill_house')
solver.add(z3.Or(*[z3.And(vacations[i] == 2, mountain_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(cigars[i] == 2, dunhill_house == i) for i in range(6)]))
solver.add(z3.Abs(mountain_house - dunhill_house) == 1)

# Clue 14: spaghetti (2) in Victorian (5) for Alice (index 4)
solver.add(house_styles[4] == 5)

# Clue 15: tall (4) loves beach (5)
for i in range(6):
    solver.add(z3.Implies(heights[i] == 4, vacations[i] == 5))

# Clue 16: tall (4) is left of Victorian (index 4)
tall_house = z3.Int('tall_house')
solver.add(z3.Or(*[z3.And(heights[i] == 4, tall_house == i) for i in range(6)]))
solver.add(tall_house < 4)

# Clue 17: stir fry (4) is directly left of Bob (4)
stir_fry_house = z3.Int('stir_fry_house')
bob_house = z3.Int('bob_house')
solver.add(z3.Or(*[z3.And(foods[i] == 4, stir_fry_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(names[i] == 4, bob_house == i) for i in range(6)]))
solver.add(bob_house == stir_fry_house + 1)

# Clue 18: modern (2) is left of Alice (index 4)
modern_house = z3.Int('modern_house')
solver.add(z3.Or(*[z3.And(house_styles[i] == 2, modern_house == i) for i in range(6)]))
solver.add(modern_house < 4)

# Clue 19: Craftsman (3) is left of short (3)
craftsman_house = z3.Int('craftsman_house')
short_house = z3.Int('short_house')
solver.add(z3.Or(*[z3.And(house_styles[i] == 3, craftsman_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(heights[i] == 3, short_house == i) for i in range(6)]))
solver.add(craftsman_house < short_house)

# Clue 20: stir fry (stir_fry_house) is left of Prince (1)
prince_house = z3.Int('prince_house')
solver.add(z3.Or(*[z3.And(cigars[i] == 1, prince_house == i) for i in range(6)]))
solver.add(stir_fry_house < prince_house)

# Clue 21: grilled cheese (3) and super tall (5) have two houses between
grilled_cheese_house = z3.Int('grilled_cheese_house')
super_tall_house = z3.Int('super_tall_house')
solver.add(z3.Or(*[z3.And(foods[i] == 3, grilled_cheese_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(heights[i] == 5, super_tall_house == i) for i in range(6)]))
solver.add(z3.Abs(grilled_cheese_house - super_tall_house) == 3)

# Clue 22: ranch (0) smokes blue master (4)
for i in range(6):
    solver.add(z3.Implies(house_styles[i] == 0, cigars[i] == 4))

# Clue 23: blends (5) is directly left of blue master (4)
solver.add(z3.Or(
    z3.And(cigars[0] == 5, cigars[1] == 4),
    z3.And(cigars[1] == 5, cigars[2] == 4),
    z3.And(cigars[2] == 5, cigars[3] == 4),
    z3.And(cigars[3] == 5, cigars[4] == 4),
    z3.And(cigars[4] == 5, cigars[5] == 4)
))

# Clue 24: cultural (0) is pizza (0)
for i in range(6):
    solver.add(z3.Implies(vacations[i] == 0, foods[i] == 0))

# Clue 25: pizza (0) is left of cruise (1)
pizza_house = z3.Int('pizza_house')
cruise_house = z3.Int('cruise_house')
solver.add(z3.Or(*[z3.And(foods[i] == 0, pizza_house == i) for i in range(6)]))
solver.add(z3.Or(*[z3.And(vacations[i] == 1, cruise_house == i) for i in range(6)]))
solver.add(pizza_house < cruise_house)

# Solve and print the result
if solver.check() == z3.sat:
    model = solver.model()

    # Mapping from integer values to strings
    name_list = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    house_style_list = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    food_list = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacation_list = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    height_list = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigar_list = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    solution_data = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }

    for house_index in range(6):
        house_number = house_index + 1
        name_val = name_list[model[names[house_index]].as_long()]
        house_style_val = house_style_list[model[house_styles[house_index]].as_long()]
        food_val = food_list[model[foods[house_index]].as_long()]
        vacation_val = vacation_list[model[vacations[house_index]].as_long()]
        height_val = height_list[model[heights[house_index]].as_long()]
        cigar_val = cigar_list[model[cigars[house_index]].as_long()]

        solution_data["solution"]["rows"].append([
            str(house_number),
            name_val,
            house_style_val,
            food_val,
            vacation_val,
            height_val,
            cigar_val
        ])

    print(json.dumps(solution_data, indent=2))
else:
    print("No solution found.")