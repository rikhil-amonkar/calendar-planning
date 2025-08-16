import json
from z3 import Solver, Int, And, Distinct

def solve():
    houses = [1, 2, 3]

    # Domains
    Names = ["Peter", "Arnold", "Eric"]
    CarModels = ["toyota camry", "ford f150", "tesla model 3"]
    HouseStyles = ["ranch", "colonial", "victorian"]
    Pets = ["cat", "dog", "fish"]
    Occupations = ["engineer", "doctor", "teacher"]
    Vacations = ["city", "mountain", "beach"]

    def var_name(prefix, label):
        return f"{prefix}_" + "".join(ch if ch.isalnum() else "_" for ch in label.lower())

    # Create position variables for each attribute value (1..3)
    posName = {n: Int(var_name("pos_name", n)) for n in Names}
    posCar = {c: Int(var_name("pos_car", c)) for c in CarModels}
    posStyle = {h: Int(var_name("pos_style", h)) for h in HouseStyles}
    posPet = {p: Int(var_name("pos_pet", p)) for p in Pets}
    posOcc = {o: Int(var_name("pos_occ", o)) for o in Occupations}
    posVac = {v: Int(var_name("pos_vac", v)) for v in Vacations}

    s = Solver()

    # Each variable in [1..3]
    for d in (posName, posCar, posStyle, posPet, posOcc, posVac):
        for v in d.values():
            s.add(And(v >= 1, v <= 3))

    # All different within each category
    s.add(Distinct([posName[n] for n in Names]))
    s.add(Distinct([posCar[c] for c in CarModels]))
    s.add(Distinct([posStyle[h] for h in HouseStyles]))
    s.add(Distinct([posPet[p] for p in Pets]))
    s.add(Distinct([posOcc[o] for o in Occupations]))
    s.add(Distinct([posVac[v] for v in Vacations]))

    # Clues:
    # 1. The person with an aquarium of fish is in the first house.
    s.add(posPet["fish"] == 1)

    # 2. The person who owns a Toyota Camry is in the second house.
    s.add(posCar["toyota camry"] == 2)

    # 3. The person who enjoys mountain retreats is not in the second house.
    s.add(posVac["mountain"] != 2)

    # 4. The person who prefers city breaks is not in the second house.
    s.add(posVac["city"] != 2)

    # 5. The person in a ranch-style home is somewhere to the left of Peter.
    s.add(posStyle["ranch"] < posName["Peter"])

    # 6. The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    s.add(posCar["toyota camry"] + 1 == posStyle["colonial"])

    # 7. Arnold is the person who has a cat.
    s.add(posName["Arnold"] == posPet["cat"])

    # 8. Eric is somewhere to the left of the person who enjoys mountain retreats.
    s.add(posName["Eric"] < posVac["mountain"])

    # 9. The person who is an engineer is not in the third house.
    s.add(posOcc["engineer"] != 3)

    # 10. The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    s.add(posCar["tesla model 3"] < posOcc["teacher"])

    # 11. The person who owns a dog is the person who is an engineer.
    s.add(posPet["dog"] == posOcc["engineer"])

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    def value_at(mapping, house):
        for k, v in mapping.items():
            if m[v].as_long() == house:
                return k
        raise RuntimeError("No value found")

    rows = []
    for h in houses:
        rows.append([
            str(h),
            value_at(posName, h),
            value_at(posCar, h),
            value_at(posStyle, h),
            value_at(posPet, h),
            value_at(posOcc, h),
            value_at(posVac, h),
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    print(json.dumps(solve(), ensure_ascii=False))