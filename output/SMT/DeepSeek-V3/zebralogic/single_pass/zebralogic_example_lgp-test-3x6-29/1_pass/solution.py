from z3 import *

def solve_puzzle():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the attributes
    names = ['Arnold', 'Peter', 'Eric']
    animals = ['bird', 'horse', 'cat']
    birthdays = ['jan', 'sept', 'april']
    hobbies = ['photography', 'cooking', 'gardening']
    drinks = ['milk', 'water', 'tea']
    hair_colors = ['black', 'brown', 'blonde']

    # Create variables for each attribute in each house
    name = {h: String(f'name_{h}') for h in houses}
    animal = {h: String(f'animal_{h}') for h in houses}
    birthday = {h: String(f'birthday_{h}') for h in houses}
    hobby = {h: String(f'hobby_{h}') for h in houses}
    drink = {h: String(f'drink_{h}') for h in houses}
    hair_color = {h: String(f'hair_color_{h}') for h in houses}

    # Add constraints that each attribute in each house must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([animal[h] == a for a in animals]))
        s.add(Or([birthday[h] == b for b in birthdays]))
        s.add(Or([hobby[h] == ho for ho in hobbies]))
        s.add(Or([drink[h] == d for d in drinks]))
        s.add(Or([hair_color[h] == hc for hc in hair_colors]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, animal, birthday, hobby, drink, hair_color]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Add constraints based on the clues
    # Clue 2: The person whose birthday is in April is in the third house.
    s.add(birthday[3] == 'april')

    # Clue 3: Eric is not in the first house.
    s.add(name[1] != 'Eric')
    s.add(Or(name[2] == 'Eric', name[3] == 'Eric'))

    # Clue 4: The cat lover is in the second house.
    s.add(animal[2] == 'cat')

    # Clue 7: The cat lover is the person who has brown hair.
    s.add(hair_color[2] == 'brown')

    # Clue 1: The person who has brown hair is the person who loves cooking.
    s.add(hobby[2] == 'cooking')

    # Clue 8: Arnold is the bird keeper.
    for h in houses:
        s.add(Implies(name[h] == 'Arnold', animal[h] == 'bird'))

    # Clue 10: The person whose birthday is in September is directly left of Arnold.
    # This means the house with birthday 'sept' is immediately to the left of the house where Arnold lives.
    # So if Arnold is in house 2, then house 1 has birthday 'sept'.
    # If Arnold is in house 3, then house 2 has birthday 'sept'.
    s.add(Or(
        And(name[2] == 'Arnold', birthday[1] == 'sept'),
        And(name[3] == 'Arnold', birthday[2] == 'sept')
    ))

    # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
    # This means the house with blonde hair has a lower number than the house that likes milk.
    s.add(Or(
        And(hair_color[1] == 'blonde', Or(drink[2] == 'milk', drink[3] == 'milk')),
        And(hair_color[2] == 'blonde', drink[3] == 'milk')
    ))

    # Clue 6: The person who enjoys gardening is the person who likes milk.
    for h in houses:
        s.add(Implies(hobby[h] == 'gardening', drink[h] == 'milk'))

    # Clue 9: The one who only drinks water is the photography enthusiast.
    for h in houses:
        s.add(Implies(drink[h] == 'water', hobby[h] == 'photography'))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": []
            }
        }
        for h in houses:
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(animal[h])),
                str(model.eval(birthday[h])),
                str(model.eval(hobby[h])),
                str(model.eval(drink[h])),
                str(model.eval(hair_color[h]))
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))