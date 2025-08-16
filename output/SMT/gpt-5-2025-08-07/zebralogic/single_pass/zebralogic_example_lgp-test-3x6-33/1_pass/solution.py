from z3 import *
import json

def solve_puzzle():
    # Index mapping for attributes
    NAMES = ["Arnold", "Eric", "Peter"]
    FLOWERS = ["carnations", "lilies", "daffodils"]
    HAIRS = ["black", "brown", "blonde"]
    SPORTS = ["soccer", "basketball", "tennis"]
    STYLES = ["colonial", "ranch", "victorian"]
    PETS = ["fish", "dog", "cat"]

    # Create Z3 solver
    s = Solver()

    # Variables: for each house (0..2), assign an index for each attribute (0..2)
    name = [Int(f"name_{i}") for i in range(3)]
    flower = [Int(f"flower_{i}") for i in range(3)]
    hair = [Int(f"hair_{i}") for i in range(3)]
    sport = [Int(f"sport_{i}") for i in range(3)]
    style = [Int(f"style_{i}") for i in range(3)]
    pet = [Int(f"pet_{i}") for i in range(3)]

    # Domain constraints (0..2)
    for arr in [name, flower, hair, sport, style, pet]:
        for v in arr:
            s.add(And(v >= 0, v <= 2))

    # Uniqueness constraints (each attribute is a permutation of 0..2)
    s.add(Distinct(name))
    s.add(Distinct(flower))
    s.add(Distinct(hair))
    s.add(Distinct(sport))
    s.add(Distinct(style))
    s.add(Distinct(pet))

    # Constants for readability
    ARNOLD, ERIC, PETER = 0, 1, 2
    CARNATIONS, LILIES, DAFFODILS = 0, 1, 2
    BLACK, BROWN, BLONDE = 0, 1, 2
    SOCCER, BASKETBALL, TENNIS = 0, 1, 2
    COLONIAL, RANCH, VICTORIAN = 0, 1, 2
    FISH, DOG, CAT = 0, 1, 2

    # Clues:
    # 2. The person who has blonde hair is in the second house.
    s.add(hair[1] == BLONDE)

    # 3. The person who loves a bouquet of daffodils is the person who has blonde hair.
    s.add(flower[1] == DAFFODILS)

    # 7. The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    # Since blonde is in house 2 (index 1), carnations is in house 1 (index 0).
    s.add(flower[0] == CARNATIONS)

    # 8. The person who loves soccer is in the third house.
    s.add(sport[2] == SOCCER)

    # 1. The person who has a cat is the person who loves soccer.
    for i in range(3):
        s.add((sport[i] == SOCCER) == (pet[i] == CAT))

    # 10. The person living in a colonial-style house is in the third house.
    s.add(style[2] == COLONIAL)

    # 5. Arnold is directly left of the person in a ranch-style home.
    s.add(Or(
        And(name[0] == ARNOLD, style[1] == RANCH),
        And(name[1] == ARNOLD, style[2] == RANCH)
    ))

    # 9. Arnold is somewhere to the left of the person who has black hair.
    s.add(Or(
        And(name[0] == ARNOLD, Or(hair[1] == BLACK, hair[2] == BLACK)),
        And(name[1] == ARNOLD, hair[2] == BLACK)
    ))

    # 4. Peter is the person who loves basketball.
    for i in range(3):
        s.add((name[i] == PETER) == (sport[i] == BASKETBALL))

    # 6. The person who owns a dog is the person who loves basketball.
    for i in range(3):
        s.add((pet[i] == DOG) == (sport[i] == BASKETBALL))

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle has no solution")

    m = s.model()

    # Build JSON solution
    header = ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
    rows = []
    for i in range(3):
        rows.append([
            str(i + 1),
            NAMES[m[name[i]].as_long()],
            FLOWERS[m[flower[i]].as_long()],
            HAIRS[m[hair[i]].as_long()],
            SPORTS[m[sport[i]].as_long()],
            STYLES[m[style[i]].as_long()],
            PETS[m[pet[i]].as_long()],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()