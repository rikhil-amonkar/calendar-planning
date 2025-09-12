from z3 import *
import json

solver = Solver()

# Define variables for each attribute's house
# Names: Eric, Peter, Arnold
eric_house = Int('eric_house')
peter_house = Int('peter_house')
arnold_house = Int('arnold_house')

# Drinks: milk, water, tea
milk_house = Int('milk_house')
water_house = Int('water_house')
tea_house = Int('tea_house')

# Vacations: mountain, city, beach
mountain_house = Int('mountain_house')
city_house = Int('city_house')
beach_house = Int('beach_house')

# HouseStyles: colonial, victorian, ranch
colonial_house = Int('colonial_house')
victorian_house = Int('victorian_house')
ranch_house = Int('ranch_house')

# Animals: cat, bird, horse
cat_house = Int('cat_house')
bird_house = Int('bird_house')
horse_house = Int('horse_house')

# Birthdays: jan, sept, april
jan_house = Int('jan_house')
sept_house = Int('sept_house')
april_house = Int('april_house')

# Add constraints for each category to have distinct houses (0-2)
def add_category_constraints(variables):
    solver.add(Distinct(variables))
    for v in variables:
        solver.add(And(v >= 0, v <= 2))

# Names
add_category_constraints([eric_house, peter_house, arnold_house])

# Drinks
add_category_constraints([milk_house, water_house, tea_house])

# Vacations
add_category_constraints([mountain_house, city_house, beach_house])

# HouseStyles
add_category_constraints([colonial_house, victorian_house, ranch_house])

# Animals
add_category_constraints([cat_house, bird_house, horse_house])

# Birthdays
add_category_constraints([jan_house, sept_house, april_house])

# Now add the clue constraints

# Clue 1: colonial < milk
solver.add(colonial_house < milk_house)

# Clue 2: city directly left of victorian → city +1 = victorian
solver.add(city_house + 1 == victorian_house)

# Clue 3: jan directly left of cat → jan +1 = cat
solver.add(jan_house + 1 == cat_house)

# Clue 4: water = mountain
solver.add(water_house == mountain_house)

# Clue 5: Peter has horse → peter_house = horse_house
solver.add(peter_house == horse_house)

# Clue 6: victorian > beach
solver.add(victorian_house > beach_house)

# Clue 7: Peter prefers city → peter_house = city_house
solver.add(peter_house == city_house)

# Clue 8: mountain = april
solver.add(mountain_house == april_house)

# Clue 9: Eric drinks water → eric_house = water_house
solver.add(eric_house == water_house)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Precompute all the house positions for each attribute
    eric_h = model.eval(eric_house).as_long()
    peter_h = model.eval(peter_house).as_long()
    arnold_h = model.eval(arnold_house).as_long()

    milk_h = model.eval(milk_house).as_long()
    water_h = model.eval(water_house).as_long()
    tea_h = model.eval(tea_house).as_long()

    mountain_h = model.eval(mountain_house).as_long()
    city_h = model.eval(city_house).as_long()
    beach_h = model.eval(beach_house).as_long()

    colonial_h = model.eval(colonial_house).as_long()
    victorian_h = model.eval(victorian_house).as_long()
    ranch_h = model.eval(ranch_house).as_long()

    cat_h = model.eval(cat_house).as_long()
    bird_h = model.eval(bird_house).as_long()
    horse_h = model.eval(horse_house).as_long()

    jan_h = model.eval(jan_house).as_long()
    sept_h = model.eval(sept_house).as_long()
    april_h = model.eval(april_house).as_long()

    # Prepare data structure for the solution
    solution_rows = []
    for h in [0, 1, 2]:
        house_num = str(h + 1)  # Convert 0-based to 1-based as string
        # Determine name
        if eric_h == h:
            name = "Eric"
        elif peter_h == h:
            name = "Peter"
        else:
            name = "Arnold"

        # Determine drink
        if milk_h == h:
            drink = "milk"
        elif water_h == h:
            drink = "water"
        else:
            drink = "tea"

        # Determine vacation
        if mountain_h == h:
            vacation = "mountain"
        elif city_h == h:
            vacation = "city"
        else:
            vacation = "beach"

        # Determine house style
        if colonial_h == h:
            house_style = "colonial"
        elif victorian_h == h:
            house_style = "victorian"
        else:
            house_style = "ranch"

        # Determine animal
        if cat_h == h:
            animal = "cat"
        elif bird_h == h:
            animal = "bird"
        else:
            animal = "horse"

        # Determine birthday
        if jan_h == h:
            birthday = "jan"
        elif sept_h == h:
            birthday = "sept"
        else:
            birthday = "april"

        solution_rows.append([house_num, name, drink, vacation, house_style, animal, birthday])

    # Build the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")