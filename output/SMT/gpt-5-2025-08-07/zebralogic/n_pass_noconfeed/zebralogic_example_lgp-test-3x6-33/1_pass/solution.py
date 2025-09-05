from z3 import *
import json

def solve_puzzle():
    # Houses indexed 0..2 representing 1..3
    n = 3
    houses = range(n)

    # Attribute domains
    Names = ["Arnold", "Eric", "Peter"]
    Flowers = ["carnations", "lilies", "daffodils"]
    HairColors = ["black", "brown", "blonde"]
    Sports = ["soccer", "basketball", "tennis"]
    HouseStyles = ["colonial", "ranch", "victorian"]
    Pets = ["fish", "dog", "cat"]

    # Index maps
    name_idx = {v: i for i, v in enumerate(Names)}
    flower_idx = {v: i for i, v in enumerate(Flowers)}
    hair_idx = {v: i for i, v in enumerate(HairColors)}
    sport_idx = {v: i for i, v in enumerate(Sports)}
    style_idx = {v: i for i, v in enumerate(HouseStyles)}
    pet_idx = {v: i for i, v in enumerate(Pets)}

    # Variables per house
    name_vars = [Int(f"name_{i}") for i in houses]
    flower_vars = [Int(f"flower_{i}") for i in houses]
    hair_vars = [Int(f"hair_{i}") for i in houses]
    sport_vars = [Int(f"sport_{i}") for i in houses]
    style_vars = [Int(f"style_{i}") for i in houses]
    pet_vars = [Int(f"pet_{i}") for i in houses]

    s = Solver()

    # Domain and AllDifferent constraints
    def add_domain_and_unique(vars_list):
        for v in vars_list:
            s.add(And(v >= 0, v < n))
        s.add(Distinct(vars_list))

    add_domain_and_unique(name_vars)
    add_domain_and_unique(flower_vars)
    add_domain_and_unique(hair_vars)
    add_domain_and_unique(sport_vars)
    add_domain_and_unique(style_vars)
    add_domain_and_unique(pet_vars)

    # Clues:
    # 1. The person who has a cat is the person who loves soccer.
    for i in houses:
        s.add((pet_vars[i] == pet_idx["cat"]) == (sport_vars[i] == sport_idx["soccer"]))

    # 2. The person who has blonde hair is in the second house.
    s.add(hair_vars[1] == hair_idx["blonde"])

    # 3. The person who loves a bouquet of daffodils is the person who has blonde hair.
    for i in houses:
        s.add((flower_vars[i] == flower_idx["daffodils"]) == (hair_vars[i] == hair_idx["blonde"]))

    # 4. Peter is the person who loves basketball.
    for i in houses:
        s.add(Implies(name_vars[i] == name_idx["Peter"], sport_vars[i] == sport_idx["basketball"]))

    # 5. Arnold is directly left of the person in a ranch-style home.
    s.add(Or(
        And(name_vars[0] == name_idx["Arnold"], style_vars[1] == style_idx["ranch"]),
        And(name_vars[1] == name_idx["Arnold"], style_vars[2] == style_idx["ranch"])
    ))

    # 6. The person who owns a dog is the person who loves basketball.
    for i in houses:
        s.add((pet_vars[i] == pet_idx["dog"]) == (sport_vars[i] == sport_idx["basketball"]))

    # 7. The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    s.add(Or(
        And(flower_vars[0] == flower_idx["carnations"], hair_vars[1] == hair_idx["blonde"]),
        And(flower_vars[1] == flower_idx["carnations"], hair_vars[2] == hair_idx["blonde"])
    ))

    # 8. The person who loves soccer is in the third house.
    s.add(sport_vars[2] == sport_idx["soccer"])

    # 9. Arnold is somewhere to the left of the person who has black hair.
    s.add(Or(
        And(name_vars[0] == name_idx["Arnold"], Or(hair_vars[1] == hair_idx["black"], hair_vars[2] == hair_idx["black"])),
        And(name_vars[1] == name_idx["Arnold"], hair_vars[2] == hair_idx["black"])
    ))

    # 10. The person living in a colonial-style house is in the third house.
    s.add(style_vars[2] == style_idx["colonial"])

    # Solve
    if s.check() != sat:
        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    def decode(vars_list, domain_list):
        return [domain_list[m.evaluate(v).as_long()] for v in vars_list]

    names_decoded = decode(name_vars, Names)
    flowers_decoded = decode(flower_vars, Flowers)
    hairs_decoded = decode(hair_vars, HairColors)
    sports_decoded = decode(sport_vars, Sports)
    styles_decoded = decode(style_vars, HouseStyles)
    pets_decoded = decode(pet_vars, Pets)

    rows = []
    for i in houses:
        row = [
            str(i + 1),
            names_decoded[i],
            flowers_decoded[i],
            hairs_decoded[i],
            sports_decoded[i],
            styles_decoded[i],
            pets_decoded[i],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()