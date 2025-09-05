import json
from z3 import *

def main():
    # Initialize the solver
    solver = Solver()
    
    # Define the attributes
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']
    
    # Create Z3 enums for each category
    NameSort, name_consts = EnumSort('Name', names)
    Arnold, Peter, Eric = name_consts
    AnimalSort, animal_consts = EnumSort('Animal', animals)
    bird, horse, cat = animal_consts
    BirthdaySort, birthday_consts = EnumSort('Birthday', birthdays)
    jan, sept, april = birthday_consts
    HobbySort, hobby_consts = EnumSort('Hobby', hobbies)
    photography, cooking, gardening = hobby_consts
    DrinkSort, drink_consts = EnumSort('Drink', drinks)
    milk, water, tea = drink_consts
    HairColorSort, hair_consts = EnumSort('HairColor', hair_colors)
    black, brown, blonde = hair_consts
    
    # Create mappings from string names to Z3 constants
    name_map = dict(zip(names, name_consts))
    animal_map = dict(zip(animals, animal_consts))
    birthday_map = dict(zip(birthdays, birthday_consts))
    hobby_map = dict(zip(hobbies, hobby_consts))
    drink_map = dict(zip(drinks, drink_consts))
    hair_map = dict(zip(hair_colors, hair_consts))
    
    # Create variables for each house attribute
    house_names = [Const(f'name_{i}', NameSort) for i in range(3)]
    house_animals = [Const(f'animal_{i}', AnimalSort) for i in range(3)]
    house_birthdays = [Const(f'birthday_{i}', BirthdaySort) for i in range(3)]
    house_hobbies = [Const(f'hobby_{i}', HobbySort) for i in range(3)]
    house_drinks = [Const(f'drink_{i}', DrinkSort) for i in range(3)]
    house_hair_colors = [Const(f'hair_color_{i}', HairColorSort) for i in range(3)]
    
    # Add uniqueness constraints
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_animals))
    solver.add(Distinct(house_birthdays))
    solver.add(Distinct(house_hobbies))
    solver.add(Distinct(house_drinks))
    solver.add(Distinct(house_hair_colors))
    
    # Clue 1: The person who has brown hair is the person who loves cooking.
    for i in range(3):
        solver.add(Implies(house_hair_colors[i] == brown, house_hobbies[i] == cooking))
    
    # Clue 2: The person whose birthday is in April is in the third house.
    solver.add(house_birthdays[2] == april)
    
    # Clue 3: Eric is not in the first house.
    solver.add(house_names[0] != Eric)
    
    # Clue 4: The cat lover is in the second house.
    solver.add(house_animals[1] == cat)
    
    # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
    blonde_left_of_milk = Or(
        And(house_hair_colors[0] == blonde, house_drinks[1] == milk),
        And(house_hair_colors[0] == blonde, house_drinks[2] == milk),
        And(house_hair_colors[1] == blonde, house_drinks[2] == milk)
    )
    solver.add(blonde_left_of_milk)
    
    # Clue 6: The person who enjoys gardening is the person who likes milk.
    for i in range(3):
        solver.add(Implies(house_hobbies[i] == gardening, house_drinks[i] == milk))
    
    # Clue 7: The cat lover is the person who has brown hair.
    for i in range(3):
        solver.add(Implies(house_animals[i] == cat, house_hair_colors[i] == brown))
    
    # Clue 8: Arnold is the bird keeper.
    for i in range(3):
        solver.add(Implies(house_names[i] == Arnold, house_animals[i] == bird))
    
    # Clue 9: The one who only drinks water is the photography enthusiast.
    for i in range(3):
        solver.add(Implies(house_drinks[i] == water, house_hobbies[i] == photography))
    
    # Clue 10: The person whose birthday is in September is directly left of Arnold.
    sept_left_arnold = Or(
        And(house_birthdays[0] == sept, house_names[1] == Arnold),
        And(house_birthdays[1] == sept, house_names[2] == Arnold)
    )
    solver.add(sept_left_arnold)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map Z3 values back to strings
        def get_value(var, model, enum_map):
            val = model[var]
            for name, z3_val in enum_map.items():
                if eq(val, z3_val):
                    return name
            return None
        
        # Collect results
        rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = get_value(house_names[i], model, name_map)
            animal_val = get_value(house_animals[i], model, animal_map)
            birthday_val = get_value(house_birthdays[i], model, birthday_map)
            hobby_val = get_value(house_hobbies[i], model, hobby_map)
            drink_val = get_value(house_drinks[i], model, drink_map)
            hair_val = get_value(house_hair_colors[i], model, hair_map)
            rows.append([house_num, name_val, animal_val, birthday_val, hobby_val, drink_val, hair_val])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()