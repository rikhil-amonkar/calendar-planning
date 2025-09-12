from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the attributes
    names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    house_styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    birthdays = ['mar', 'sept', 'may', 'feb', 'jan', 'april']
    
    # Create integer variables for each attribute position
    name_vars = [Int(f'name_{name}') for name in names]
    pet_vars = [Int(f'pet_{pet}') for pet in pets]
    style_vars = [Int(f'style_{style}') for style in house_styles]
    birthday_vars = [Int(f'birthday_{bday}') for bday in birthdays]
    
    # All positions must be between 1 and 6
    for var in name_vars + pet_vars + style_vars + birthday_vars:
        solver.add(And(var >= 1, var <= 6))
    
    # All positions within each category must be distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(pet_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(birthday_vars))
    
    # Create variables for each house's attributes
    house_names = [Int(f'house_{i}_name') for i in range(1, 7)]
    house_pets = [Int(f'house_{i}_pet') for i in range(1, 7)]
    house_styles_var = [Int(f'house_{i}_style') for i in range(1, 7)]
    house_birthdays = [Int(f'house_{i}_birthday') for i in range(1, 7)]
    
    # Link position variables to house variables
    for i, name in enumerate(names):
        for house in range(1, 7):
            solver.add(Implies(name_vars[i] == house, house_names[house-1] == i))
    
    for i, pet in enumerate(pets):
        for house in range(1, 7):
            solver.add(Implies(pet_vars[i] == house, house_pets[house-1] == i))
    
    for i, style in enumerate(house_styles):
        for house in range(1, 7):
            solver.add(Implies(style_vars[i] == house, house_styles_var[house-1] == i))
    
    for i, bday in enumerate(birthdays):
        for house in range(1, 7):
            solver.add(Implies(birthday_vars[i] == house, house_birthdays[house-1] == i))
    
    # Clue 1: The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
    hamster_pos = pet_vars[pets.index('hamster')]
    mar_bday_pos = birthday_vars[birthdays.index('mar')]
    solver.add(hamster_pos > mar_bday_pos)
    
    # Clue 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
    jan_bday_pos = birthday_vars[birthdays.index('jan')]
    sept_bday_pos = birthday_vars[birthdays.index('sept')]
    solver.add(jan_bday_pos < sept_bday_pos)
    
    # Clue 3: The person whose birthday is in May is in the second house.
    may_bday_pos = birthday_vars[birthdays.index('may')]
    solver.add(may_bday_pos == 2)
    
    # Clue 4: The person living in a colonial-style house is in the second house.
    colonial_style_pos = style_vars[house_styles.index('colonial')]
    solver.add(colonial_style_pos == 2)
    
    # Clue 5: Carol is in the third house.
    carol_pos = name_vars[names.index('Carol')]
    solver.add(carol_pos == 3)
    
    # Clue 6: The person in a Mediterranean-style villa is not in the sixth house.
    mediterranean_style_pos = style_vars[house_styles.index('mediterranean')]
    solver.add(mediterranean_style_pos != 6)
    
    # Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
    fish_pos = pet_vars[pets.index('fish')]
    bob_pos = name_vars[names.index('Bob')]
    solver.add(fish_pos > bob_pos)
    
    # Clue 8: Eric is in the sixth house.
    eric_pos = name_vars[names.index('Eric')]
    solver.add(eric_pos == 6)
    
    # Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
    cat_pos = pet_vars[pets.index('cat')]
    victorian_style_pos = style_vars[house_styles.index('victorian')]
    solver.add(Or(cat_pos == victorian_style_pos + 2, cat_pos == victorian_style_pos - 2))
    
    # Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
    solver.add(Or(victorian_style_pos == hamster_pos + 3, victorian_style_pos == hamster_pos - 3))
    
    # Clue 11: The person in a Craftsman-style house is Arnold.
    craftsman_style_pos = style_vars[house_styles.index('craftsman')]
    arnold_pos = name_vars[names.index('Arnold')]
    solver.add(craftsman_style_pos == arnold_pos)
    
    # Clue 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
    modern_style_pos = style_vars[house_styles.index('modern')]
    solver.add(colonial_style_pos < modern_style_pos)
    
    # Clue 13: The person with an aquarium of fish is not in the second house.
    solver.add(fish_pos != 2)
    
    # Clue 14: Peter is the person living in a colonial-style house.
    peter_pos = name_vars[names.index('Peter')]
    solver.add(peter_pos == colonial_style_pos)
    
    # Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
    april_bday_pos = birthday_vars[birthdays.index('april')]
    solver.add(jan_bday_pos + 1 == april_bday_pos)
    
    # Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
    bird_pos = pet_vars[pets.index('bird')]
    solver.add(Or(bird_pos == modern_style_pos + 2, bird_pos == modern_style_pos - 2))
    
    # Clue 17: Carol is the person whose birthday is in March.
    solver.add(carol_pos == mar_bday_pos)
    
    # Clue 18: The person in a Craftsman-style house is in the fourth house.
    solver.add(craftsman_style_pos == 4)
    
    # Clue 19: The person who owns a dog is in the fourth house.
    dog_pos = pet_vars[pets.index('dog')]
    solver.add(dog_pos == 4)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Create result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in range(1, 7):
            name_idx = model.eval(house_names[house-1]).as_long()
            pet_idx = model.eval(house_pets[house-1]).as_long()
            style_idx = model.eval(house_styles_var[house-1]).as_long()
            birthday_idx = model.eval(house_birthdays[house-1]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                pets[pet_idx],
                house_styles[style_idx],
                birthdays[birthday_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()