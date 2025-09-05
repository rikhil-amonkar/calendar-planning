import json
from z3 import *

def main():
    solver = Solver()
    num_houses = 3

    # Create Z3 integer variables for each attribute of the houses.
    names = [Int(f"name_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]
    hair = [Int(f"hair_{i}") for i in range(num_houses)]
    sports = [Int(f"sport_{i}") for i in range(num_houses)]
    styles = [Int(f"style_{i}") for i in range(num_houses)]
    pets = [Int(f"pet_{i}") for i in range(num_houses)]

    # All variables are in the domain {0, 1, 2}
    for group in [names, flowers, hair, sports, styles, pets]:
        for var in group:
            solver.add(var >= 0, var <= 2)

    # Enforce that each attribute is unique across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(flowers))
    solver.add(Distinct(hair))
    solver.add(Distinct(sports))
    solver.add(Distinct(styles))
    solver.add(Distinct(pets))

    # Mappings (used later for output):
    # Names: 0:"Arnold", 1:"Eric", 2:"Peter"
    # Flowers: 0:"carnations", 1:"lilies", 2:"daffodils"
    # HairColors: 0:"black", 1:"brown", 2:"blonde"
    # FavoriteSports: 0:"soccer", 1:"basketball", 2:"tennis"
    # HouseStyles: 0:"colonial", 1:"ranch", 2:"victorian"
    # Pets: 0:"fish", 1:"dog", 2:"cat"

    # Clue 1: The person who has a cat is the person who loves soccer.
    for i in range(num_houses):
        solver.add(Implies(pets[i] == 2, sports[i] == 0))
        solver.add(Implies(sports[i] == 0, pets[i] == 2))

    # Clue 2: The person who has blonde hair is in the second house.
    solver.add(hair[1] == 2)

    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    for i in range(num_houses):
        solver.add(Implies(flowers[i] == 2, hair[i] == 2))
        solver.add(Implies(hair[i] == 2, flowers[i] == 2))

    # Clue 4: Peter is the person who loves basketball.
    for i in range(num_houses):
        solver.add(Implies(names[i] == 2, sports[i] == 1))
        solver.add(Implies(sports[i] == 1, names[i] == 2))

    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    # This means either:
    #   - House 1 is Arnold (0) and House 2 is ranch (1) OR
    #   - House 0 is Arnold (0) and House 1 is ranch (1)
    solver.add(Or(And(names[0] == 0, styles[1] == 1),
                  And(names[1] == 0, styles[2] == 1)))

    # Clue 6: The person who owns a dog is the person who loves basketball.
    for i in range(num_houses):
        solver.add(Implies(pets[i] == 1, sports[i] == 1))
        solver.add(Implies(sports[i] == 1, pets[i] == 1))

    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    # That is, either House 1's flower is carnations (0) and House 2 has blonde hair (2),
    # or House 0's flower is carnations (0) and House 1 has blonde hair (2).
    solver.add(Or(And(flowers[0] == 0, hair[1] == 2),
                  And(flowers[1] == 0, hair[2] == 2)))

    # Clue 8: The person who loves soccer is in the third house.
    solver.add(sports[2] == 0)

    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    # Since houses are ordered from 1 (leftmost) to 3 (rightmost),
    # Arnold cannot be in the third house.
    solver.add(Not(names[2] == 0))
    solver.add(Implies(names[0] == 0, Or(hair[1] == 0, hair[2] == 0)))
    solver.add(Implies(names[1] == 0, hair[2] == 0))

    # Clue 10: The person living in a colonial-style house is in the third house.
    solver.add(styles[2] == 0)

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()

        # Define mappings from code to actual attribute strings.
        name_map = {0: "Arnold", 1: "Eric", 2: "Peter"}
        flower_map = {0: "carnations", 1: "lilies", 2: "daffodils"}
        hair_map = {0: "black", 1: "brown", 2: "blonde"}
        sport_map = {0: "soccer", 1: "basketball", 2: "tennis"}
        style_map = {0: "colonial", 1: "ranch", 2: "victorian"}
        pet_map = {0: "fish", 1: "dog", 2: "cat"}

        # Build the rows with house numbers 1, 2, 3 in order.
        rows = []
        for i in range(num_houses):
            row = [
                str(i + 1),
                name_map[model[names[i]].as_long()],
                flower_map[model[flowers[i]].as_long()],
                hair_map[model[hair[i]].as_long()],
                sport_map[model[sports[i]].as_long()],
                style_map[model[styles[i]].as_long()],
                pet_map[model[pets[i]].as_long()]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()