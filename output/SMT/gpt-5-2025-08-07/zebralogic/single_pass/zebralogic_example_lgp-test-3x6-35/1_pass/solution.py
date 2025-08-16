# Requires: z3-solver
from z3 import *
import json

def main():
    s = Solver()

    def var(name):
        v = Int(name)
        s.add(And(v >= 1, v <= 3))
        return v

    # Names
    n = {
        "Eric": var("n_Eric"),
        "Arnold": var("n_Arnold"),
        "Peter": var("n_Peter"),
    }
    s.add(Distinct(*n.values()))

    # Vacation
    vac = {
        "mountain": var("vac_mountain"),
        "city": var("vac_city"),
        "beach": var("vac_beach"),
    }
    s.add(Distinct(*vac.values()))

    # Height
    height = {
        "very short": var("height_very_short"),
        "average": var("height_average"),
        "short": var("height_short"),
    }
    s.add(Distinct(*height.values()))

    # Flower
    flower = {
        "carnations": var("flower_carnations"),
        "daffodils": var("flower_daffodils"),
        "lilies": var("flower_lilies"),
    }
    s.add(Distinct(*flower.values()))

    # Hair color
    hair = {
        "brown": var("hair_brown"),
        "black": var("hair_black"),
        "blonde": var("hair_blonde"),
    }
    s.add(Distinct(*hair.values()))

    # Education
    edu = {
        "associate": var("edu_associate"),
        "bachelor": var("edu_bachelor"),
        "high school": var("edu_high_school"),
    }
    s.add(Distinct(*edu.values()))

    # Clues:
    # 1. Peter is the person who has an average height.
    s.add(n["Peter"] == height["average"])
    # 2. The person who loves a bouquet of daffodils is Arnold.
    s.add(flower["daffodils"] == n["Arnold"])
    # 3. The person who is very short is not in the second house.
    s.add(height["very short"] != 2)
    # 4. The person who loves beach vacations is in the first house.
    s.add(vac["beach"] == 1)
    # 5. The person with a high school diploma is in the third house.
    s.add(edu["high school"] == 3)
    # 6. The person who is short is somewhere to the right of the person who is very short.
    s.add(height["short"] > height["very short"])
    # 7. The person who loves the bouquet of lilies is Eric.
    s.add(flower["lilies"] == n["Eric"])
    # 8. The person who loves the bouquet of lilies is the person with a bachelor's degree.
    s.add(flower["lilies"] == edu["bachelor"])
    # 9. The person who prefers city breaks is somewhere to the right of Peter.
    s.add(vac["city"] > n["Peter"])
    # 10. The person who has blonde hair is in the third house.
    s.add(hair["blonde"] == 3)
    # 11. The person who loves beach vacations is the person who has brown hair.
    s.add(vac["beach"] == hair["brown"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    def invert(mapping, house_idx):
        # Return the key whose variable equals the given house index
        for k, v in mapping.items():
            if m.evaluate(v).as_long() == house_idx:
                return k
        return None

    rows = []
    for h in [1, 2, 3]:
        name = invert(n, h)
        vacation = invert(vac, h)
        hgt = invert(height, h)
        flw = invert(flower, h)
        hr = invert(hair, h)
        ed = invert(edu, h)
        rows.append([str(h), name, vacation, hgt, flw, hr, ed])

    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(solution))

if __name__ == "__main__":
    main()