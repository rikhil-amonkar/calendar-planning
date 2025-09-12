import json
from z3 import *

def main():
    # Create the solver
    s = Solver()

    # Define the attributes and their possible values
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['milk', 'water', 'tea']
    vacations = ['mountain', 'city', 'beach']
    house_styles = ['colonial', 'victorian', 'ranch']
    animals = ['cat', 'bird', 'horse']
    birthdays = ['jan', 'sept', 'april']

    # Create integer variables for each attribute for each house
    name_vars = [Int(f"name_{i}") for i in range(1,4)]
    drink_vars = [Int(f"drink_{i}") for i in range(1,4)]
    vacation_vars = [Int(f"vacation_{i}") for i in range(1,4)]
    style_vars = [Int(f"style_{i}") for i in range(1,4)]
    animal_vars = [Int(f"animal_{i}") for i in range(1,4)]
    birthday_vars = [Int(f"birthday_{i}") for i in range(1,4)]

    # Add constraints that each attribute variable is between 0 and 2
    for var in name_vars + drink_vars + vacation_vars + style_vars + animal_vars + birthday_vars:
        s.add(var >= 0, var < 3)

    # Add constraints that all attributes are distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(drink_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(style_vars))
    s.add(Distinct(animal_vars))
    s.add(Distinct(birthday_vars))

    # Clue 1: The person in colonial is left of milk drinker
    colonial_index = house_styles.index('colonial')
    milk_index = drinks.index('milk')
    s.add(Or(
        And(style_vars[0] == colonial_index, drink_vars[1] == milk_index),
        And(style_vars[0] == colonial_index, drink_vars[2] == milk_index),
        And(style_vars[1] == colonial_index, drink_vars[2] == milk_index)
    ))

    # Clue 2: City vacation is directly left of Victorian house
    city_index = vacations.index('city')
    victorian_index = house_styles.index('victorian')
    s.add(Or(
        And(vacation_vars[0] == city_index, style_vars[1] == victorian_index),
        And(vacation_vars[1] == city_index, style_vars[2] == victorian_index)
    ))

    # Clue 3: January birthday directly left of cat lover
    jan_index = birthdays.index('jan')
    cat_index = animals.index('cat')
    s.add(Or(
        And(birthday_vars[0] == jan_index, animal_vars[1] == cat_index),
        And(birthday_vars[1] == jan_index, animal_vars[2] == cat_index)
    ))

    # Clue 4: Water drinker is mountain vacationer
    water_index = drinks.index('water')
    mountain_index = vacations.index('mountain')
    for i in range(3):
        s.add(Implies(drink_vars[i] == water_index, vacation_vars[i] == mountain_index))

    # Clue 5: Horse keeper is Peter
    horse_index = animals.index('horse')
    peter_index = names.index('Peter')
    for i in range(3):
        s.add(Implies(animal_vars[i] == horse_index, name_vars[i] == peter_index))

    # Clue 6: Victorian house is right of beach vacationer
    beach_index = vacations.index('beach')
    s.add(Or(
        And(vacation_vars[0] == beach_index, style_vars[1] == victorian_index),
        And(vacation_vars[0] == beach_index, style_vars[2] == victorian_index),
        And(vacation_vars[1] == beach_index, style_vars[2] == victorian_index)
    ))

    # Clue 7: Peter prefers city breaks
    s.add(Or([And(name_vars[i] == peter_index, vacation_vars[i] == city_index) for i in range(3)]))

    # Clue 8: Mountain vacationer has April birthday
    april_index = birthdays.index('april')
    for i in range(3):
        s.add(Implies(vacation_vars[i] == mountain_index, birthday_vars[i] == april_index))

    # Clue 9: Eric drinks water
    eric_index = names.index('Eric')
    for i in range(3):
        s.add(Implies(name_vars[i] == eric_index, drink_vars[i] == water_index))

    # Check and get the solution
    if s.check() == sat:
        model = s.model()
        
        # Map house numbers to attribute values
        solution = []
        for i in range(3):
            house_num = str(i+1)
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            drink_val = drinks[model.evaluate(drink_vars[i]).as_long()]
            vacation_val = vacations[model.evaluate(vacation_vars[i]).as_long()]
            style_val = house_styles[model.evaluate(style_vars[i]).as_long()]
            animal_val = animals[model.evaluate(animal_vars[i]).as_long()]
            birthday_val = birthdays[model.evaluate(birthday_vars[i]).as_long()]
            
            solution.append([house_num, name_val, drink_val, vacation_val, style_val, animal_val, birthday_val])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()