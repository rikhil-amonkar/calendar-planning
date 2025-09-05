import json
from z3 import Solver, Int, Distinct, sat

def main():
    s = Solver()

    # Name variables: each house is 1,2,3.
    Arnold = Int("Arnold")
    Peter = Int("Peter")
    Eric = Int("Eric")
    s.add(Arnold >= 1, Arnold <= 3,
          Peter >= 1, Peter <= 3,
          Eric >= 1, Eric <= 3,
          Distinct(Arnold, Peter, Eric))

    # Animal variables:
    bird = Int("bird")
    horse = Int("horse")
    cat = Int("cat")
    s.add(bird >= 1, bird <= 3,
          horse >= 1, horse <= 3,
          cat >= 1, cat <= 3,
          Distinct(bird, horse, cat))

    # Birthday variables:
    jan = Int("jan")
    sept = Int("sept")
    april = Int("april")
    s.add(jan >= 1, jan <= 3,
          sept >= 1, sept <= 3,
          april >= 1, april <= 3,
          Distinct(jan, sept, april))

    # Hobby variables:
    photography = Int("photography")
    cooking = Int("cooking")
    gardening = Int("gardening")
    s.add(photography >= 1, photography <= 3,
          cooking >= 1, cooking <= 3,
          gardening >= 1, gardening <= 3,
          Distinct(photography, cooking, gardening))

    # Drink variables:
    milk = Int("milk")
    water = Int("water")
    tea = Int("tea")
    s.add(milk >= 1, milk <= 3,
          water >= 1, water <= 3,
          tea >= 1, tea <= 3,
          Distinct(milk, water, tea))

    # HairColor variables:
    black = Int("black")
    brown = Int("brown")
    blonde = Int("blonde")
    s.add(black >= 1, black <= 3,
          brown >= 1, brown <= 3,
          blonde >= 1, blonde <= 3,
          Distinct(black, brown, blonde))

    # Clue 1: The person who has brown hair is the person who loves cooking.
    s.add(brown == cooking)

    # Clue 2: The person whose birthday is in April is in the third house.
    s.add(april == 3)

    # Clue 3: Eric is not in the first house.
    s.add(Eric != 1)

    # Clue 4: The cat lover is in the second house.
    s.add(cat == 2)

    # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
    s.add(blonde < milk)

    # Clue 6: The person who enjoys gardening is the person who likes milk.
    s.add(gardening == milk)

    # Clue 7: The cat lover is the person who has brown hair.
    s.add(cat == brown)

    # Clue 8: Arnold is the bird keeper.
    s.add(Arnold == bird)

    # Clue 9: The one who only drinks water is the photography enthusiast.
    s.add(water == photography)

    # Clue 10: The person whose birthday is in September is directly left of Arnold.
    s.add(sept + 1 == Arnold)

    if s.check() == sat:
        m = s.model()

        # Build mappings: attribute_value -> house number.
        names = {
            "Arnold": m[Arnold].as_long(),
            "Peter": m[Peter].as_long(),
            "Eric": m[Eric].as_long()
        }
        animals = {
            "bird": m[bird].as_long(),
            "horse": m[horse].as_long(),
            "cat": m[cat].as_long()
        }
        birthdays = {
            "jan": m[jan].as_long(),
            "sept": m[sept].as_long(),
            "april": m[april].as_long()
        }
        hobbies = {
            "photography": m[photography].as_long(),
            "cooking": m[cooking].as_long(),
            "gardening": m[gardening].as_long()
        }
        drinks = {
            "milk": m[milk].as_long(),
            "water": m[water].as_long(),
            "tea": m[tea].as_long()
        }
        haircolors = {
            "black": m[black].as_long(),
            "brown": m[brown].as_long(),
            "blonde": m[blonde].as_long()
        }

        # Prepare solution rows for houses 1 to 3
        solution_rows = []
        for house in range(1, 4):
            name_val = [name for name, pos in names.items() if pos == house][0]
            animal_val = [pet for pet, pos in animals.items() if pos == house][0]
            birthday_val = [bday for bday, pos in birthdays.items() if pos == house][0]
            hobby_val = [h for h, pos in hobbies.items() if pos == house][0]
            drink_val = [d for d, pos in drinks.items() if pos == house][0]
            haircolor_val = [hc for hc, pos in haircolors.items() if pos == house][0]
            solution_rows.append([
                str(house),
                name_val,
                animal_val,
                birthday_val,
                hobby_val,
                drink_val,
                haircolor_val
            ])

        result = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()