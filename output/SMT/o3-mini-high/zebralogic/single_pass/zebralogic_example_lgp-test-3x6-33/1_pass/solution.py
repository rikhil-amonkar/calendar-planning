from z3 import *
import json

def main():
    s = Solver()
    houses = range(3)  # We have three houses: indices 0, 1, 2 which correspond to Houses 1, 2, 3 respectively.

    # Create an integer variable for each attribute in every house.
    # The domain for each variable is {0,1,2}.
    # We choose the following mappings:
    #   Name:         Arnold = 0, Eric = 1, Peter = 2
    #   Flower:       carnations = 0, daffodils = 1, lilies = 2
    #   HairColor:    black = 0, brown = 1, blonde = 2
    #   FavoriteSport: soccer = 0, basketball = 1, tennis = 2
    #   HouseStyle:   colonial = 0, ranch = 1, victorian = 2
    #   Pet:          fish = 0, dog = 1, cat = 2
    name  = [Int(f"name_{i}") for i in houses]
    flower = [Int(f"flower_{i}") for i in houses]
    hair  = [Int(f"hair_{i}") for i in houses]
    sport = [Int(f"sport_{i}") for i in houses]
    style = [Int(f"style_{i}") for i in houses]
    pet   = [Int(f"pet_{i}") for i in houses]

    for group in [name, flower, hair, sport, style, pet]:
        for var in group:
            s.add(And(var >= 0, var <= 2))

    # All houses must have distinct values for each category.
    s.add(Distinct(name))
    s.add(Distinct(flower))
    s.add(Distinct(hair))
    s.add(Distinct(sport))
    s.add(Distinct(style))
    s.add(Distinct(pet))

    # Clue 1: "The person who has a cat is the person who loves soccer."
    # In our mapping: cat = 2 and soccer = 0.
    for i in houses:
        s.add(Implies(pet[i] == 2, sport[i] == 0))
        s.add(Implies(sport[i] == 0, pet[i] == 2))

    # Clue 2: "The person who has blonde hair is in the second house."
    # House 2 => index 1. Blonde hair = 2.
    s.add(hair[1] == 2)

    # Clue 3: "The person who loves a bouquet of daffodils is the person who has blonde hair."
    # Daffodils = 1, so for any house, blonde hair <=> daffodils.
    for i in houses:
        s.add(Implies(hair[i] == 2, flower[i] == 1))
        s.add(Implies(flower[i] == 1, hair[i] == 2))

    # Clue 4: "Peter is the person who loves basketball."
    # Peter = 2 and basketball = 1.
    for i in houses:
        s.add(Implies(name[i] == 2, sport[i] == 1))
        s.add(Implies(sport[i] == 1, name[i] == 2))

    # Clue 5: "Arnold is directly left of the person in a ranch-style home."
    # Arnold = 0 and ranch = 1. Possibilities:
    #   Either House1 (index 0) is Arnold and House2 (index 1) has ranch,
    #   or House2 (index 1) is Arnold and House3 (index 2) has ranch.
    s.add(Or(And(name[0] == 0, style[1] == 1),
             And(name[1] == 0, style[2] == 1)))

    # Clue 6: "The person who owns a dog is the person who loves basketball."
    # Dog = 1 and basketball = 1.
    for i in houses:
        s.add(Implies(pet[i] == 1, sport[i] == 1))
        s.add(Implies(sport[i] == 1, pet[i] == 1))

    # Clue 7: "The person who loves a carnations arrangement is directly left of the person who has blonde hair."
    # Carnations = 0. 'Directly left' means adjacent house.
    # Either House1 (index 0) must have carnations and House2 (index 1) blonde,
    # or House2 (index 1) has carnations and House3 (index 2) blonde.
    s.add(Or(And(flower[0] == 0, hair[1] == 2),
             And(flower[1] == 0, hair[2] == 2)))
    # Given that House2 is already forced to have blonde hair (clue 2), the only possibility is:
    s.add(flower[0] == 0)

    # Clue 8: "The person who loves soccer is in the third house."
    # Third house => index 2 and soccer = 0.
    s.add(sport[2] == 0)

    # Clue 9: "Arnold is somewhere to the left of the person who has black hair."
    # Arnold = 0 and black = 0. This means that if Arnold is in house i and black-haired person is in house j then i < j.
    # Possibilities:
    #   Either House1 (index 0) is Arnold and either House2 or House3 has black hair,
    #   or House2 (index 1) is Arnold and House3 has black hair.
    s.add(Or(And(name[0] == 0, Or(hair[1] == 0, hair[2] == 0)),
             And(name[1] == 0, hair[2] == 0)))

    # Clue 10: "The person living in a colonial-style house is in the third house."
    # Colonial = 0 so House3 (index 2) has colonial style.
    s.add(style[2] == 0)

    # Additional direct consequences:
    # From Clues 2 and 3, House2 (index 1) must have daffodils.
    s.add(flower[1] == 1)

    # Solve and print out the solution in the required JSON format.
    if s.check() == sat:
        m = s.model()

        # Define mapping dictionaries to convert numeric assignments back to strings.
        name_map   = {0: "Arnold", 1: "Eric", 2: "Peter"}
        flower_map = {0: "carnations", 1: "daffodils", 2: "lilies"}
        hair_map   = {0: "black", 1: "brown", 2: "blonde"}
        sport_map  = {0: "soccer", 1: "basketball", 2: "tennis"}
        style_map  = {0: "colonial", 1: "ranch", 2: "victorian"}
        pet_map    = {0: "fish", 1: "dog", 2: "cat"}

        # Build the rows for houses 1, 2, and 3 (in order).
        rows = []
        for i in houses:
            row = [
                str(i+1),
                name_map[m[name[i]].as_long()],
                flower_map[m[flower[i]].as_long()],
                hair_map[m[hair[i]].as_long()],
                sport_map[m[sport[i]].as_long()],
                style_map[m[style[i]].as_long()],
                pet_map[m[pet[i]].as_long()]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()