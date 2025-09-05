import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for Names
    Peter = Int('Peter')
    Bob = Int('Bob')
    Carol = Int('Carol')
    Eric = Int('Eric')
    Alice = Int('Alice')
    Arnold = Int('Arnold')
    names_vars = [Peter, Bob, Carol, Eric, Alice, Arnold]

    # Define variables for Pets
    pet_bird = Int('pet_bird')
    pet_dog = Int('pet_dog')
    pet_cat = Int('pet_cat')
    pet_rabbit = Int('pet_rabbit')
    pet_fish = Int('pet_fish')
    pet_hamster = Int('pet_hamster')
    pet_vars = [pet_bird, pet_dog, pet_cat, pet_rabbit, pet_fish, pet_hamster]

    # Define variables for House Styles
    style_victorian = Int('style_victorian')
    style_ranch = Int('style_ranch')
    style_modern = Int('style_modern')
    style_mediterranean = Int('style_mediterranean')
    style_colonial = Int('style_colonial')
    style_craftsman = Int('style_craftsman')
    style_vars = [style_victorian, style_ranch, style_modern, style_mediterranean, style_colonial, style_craftsman]

    # Define variables for Birthdays
    birthday_mar = Int('birthday_mar')
    birthday_sept = Int('birthday_sept')
    birthday_may = Int('birthday_may')
    birthday_feb = Int('birthday_feb')
    birthday_jan = Int('birthday_jan')
    birthday_april = Int('birthday_april')
    birthday_vars = [birthday_mar, birthday_sept, birthday_may, birthday_feb, birthday_jan, birthday_april]

    # All variables must take a value from 1 to 6 (houses 1 to 6)
    for var in names_vars + pet_vars + style_vars + birthday_vars:
        solver.add(And(var >= 1, var <= 6))

    # All values in each category are distinct
    solver.add(Distinct(*names_vars))
    solver.add(Distinct(*pet_vars))
    solver.add(Distinct(*style_vars))
    solver.add(Distinct(*birthday_vars))

    # Clue 1: The person with a pet hamster is somewhere to the right of the person whose birthday is in March.
    solver.add(pet_hamster > birthday_mar)

    # Clue 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
    solver.add(birthday_jan < birthday_sept)

    # Clue 3: The person whose birthday is in May is in the second house.
    solver.add(birthday_may == 2)

    # Clue 4: The person living in a colonial-style house is in the second house.
    solver.add(style_colonial == 2)

    # Clue 5: Carol is in the third house.
    solver.add(Carol == 3)

    # Clue 6: The person in a Mediterranean-style villa is not in the sixth house.
    solver.add(style_mediterranean != 6)

    # Clue 7: The person with an aquarium of fish is somewhere to the right of Bob.
    solver.add(pet_fish > Bob)

    # Clue 8: Eric is in the sixth house.
    solver.add(Eric == 6)

    # Clue 9: There is one house between the person who has a cat and the person residing in a Victorian house.
    solver.add(Abs(pet_cat - style_victorian) == 2)

    # Clue 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
    solver.add(Abs(style_victorian - pet_hamster) == 3)

    # Clue 11: The person in a Craftsman-style house is Arnold.
    solver.add(style_craftsman == Arnold)

    # Clue 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
    solver.add(style_colonial < style_modern)

    # Clue 13: The person with an aquarium of fish is not in the second house.
    solver.add(pet_fish != 2)

    # Clue 14: Peter is the person living in a colonial-style house.
    solver.add(Peter == style_colonial)

    # Clue 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
    solver.add(birthday_jan + 1 == birthday_april)

    # Clue 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
    solver.add(Abs(pet_bird - style_modern) == 2)

    # Clue 17: Carol is the person whose birthday is in March.
    solver.add(Carol == birthday_mar)

    # Clue 18: The person in a Craftsman-style house is in the fourth house.
    solver.add(style_craftsman == 4)

    # Clue 19: The person who owns a dog is in the fourth house.
    solver.add(pet_dog == 4)

    # Try to solve the puzzle.
    if solver.check() == sat:
        m = solver.model()

        # Build a mapping for each house (1 to 6) for each attribute
        houses = {i: {} for i in range(1, 7)}

        # Map Names to houses
        names_map = [("Peter", Peter), ("Bob", Bob), ("Carol", Carol), ("Eric", Eric), ("Alice", Alice), ("Arnold", Arnold)]
        for name, var in names_map:
            houses[m[var].as_long()]["Name"] = name

        # Map Pets to houses
        pets_map = [("bird", pet_bird), ("dog", pet_dog), ("cat", pet_cat), ("rabbit", pet_rabbit), ("fish", pet_fish), ("hamster", pet_hamster)]
        for pet, var in pets_map:
            houses[m[var].as_long()]["Pet"] = pet

        # Map House Styles to houses
        styles_map = [("victorian", style_victorian), ("ranch", style_ranch), ("modern", style_modern), ("mediterranean", style_mediterranean), ("colonial", style_colonial), ("craftsman", style_craftsman)]
        for style, var in styles_map:
            houses[m[var].as_long()]["HouseStyle"] = style

        # Map Birthdays to houses
        birthdays_map = [("mar", birthday_mar), ("sept", birthday_sept), ("may", birthday_may), ("feb", birthday_feb), ("jan", birthday_jan), ("april", birthday_april)]
        for bd, var in birthdays_map:
            houses[m[var].as_long()]["Birthday"] = bd

        # Assemble the rows in the required order
        header = ["House", "Name", "Pet", "HouseStyle", "Birthday"]
        rows = []
        for i in range(1, 7):
            row = [
                str(i),
                houses[i].get("Name", ""),
                houses[i].get("Pet", ""),
                houses[i].get("HouseStyle", ""),
                houses[i].get("Birthday", "")
            ]
            rows.append(row)

        solution = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()