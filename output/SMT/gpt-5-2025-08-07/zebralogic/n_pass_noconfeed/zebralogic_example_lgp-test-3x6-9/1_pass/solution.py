import json
from z3 import Solver, Int, And, Distinct, sat

def sanitize(name):
    return ''.join(ch if ch.isalnum() else '_' for ch in name)

def main():
    houses = [1, 2, 3]

    # Categories and values
    Names = ["Peter", "Arnold", "Eric"]
    CarModels = ["toyota camry", "ford f150", "tesla model 3"]
    HouseStyles = ["ranch", "colonial", "victorian"]
    Pets = ["cat", "dog", "fish"]
    Occupations = ["engineer", "doctor", "teacher"]
    Vacations = ["city", "mountain", "beach"]

    # Create Z3 variables (each value is assigned a house position 1..3)
    def mk_vars(category, values):
        return {val: Int(f"{sanitize(category)}_{sanitize(val)}") for val in values}

    name_vars = mk_vars("Name", Names)
    car_vars = mk_vars("CarModel", CarModels)
    style_vars = mk_vars("HouseStyle", HouseStyles)
    pet_vars = mk_vars("Pet", Pets)
    occ_vars = mk_vars("Occupation", Occupations)
    vac_vars = mk_vars("Vacation", Vacations)

    s = Solver()

    # Domains
    for var in list(name_vars.values()) + list(car_vars.values()) + list(style_vars.values()) + \
               list(pet_vars.values()) + list(occ_vars.values()) + list(vac_vars.values()):
        s.add(And(var >= 1, var <= 3))

    # Uniqueness within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*car_vars.values()))
    s.add(Distinct(*style_vars.values()))
    s.add(Distinct(*pet_vars.values()))
    s.add(Distinct(*occ_vars.values()))
    s.add(Distinct(*vac_vars.values()))

    # Clues:
    # 1. The person with an aquarium of fish is in the first house.
    s.add(pet_vars["fish"] == 1)

    # 2. The person who owns a Toyota Camry is in the second house.
    s.add(car_vars["toyota camry"] == 2)

    # 3. The person who enjoys mountain retreats is not in the second house.
    s.add(vac_vars["mountain"] != 2)

    # 4. The person who prefers city breaks is not in the second house.
    s.add(vac_vars["city"] != 2)

    # 5. The person in a ranch-style home is somewhere to the left of Peter.
    s.add(style_vars["ranch"] < name_vars["Peter"])

    # 6. The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    s.add(car_vars["toyota camry"] + 1 == style_vars["colonial"])

    # 7. Arnold is the person who has a cat.
    s.add(name_vars["Arnold"] == pet_vars["cat"])

    # 8. Eric is somewhere to the left of the person who enjoys mountain retreats.
    s.add(name_vars["Eric"] < vac_vars["mountain"])

    # 9. The person who is an engineer is not in the third house.
    s.add(occ_vars["engineer"] != 3)

    # 10. The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    s.add(car_vars["tesla model 3"] < occ_vars["teacher"])

    # 11. The person who owns a dog is the person who is an engineer.
    s.add(pet_vars["dog"] == occ_vars["engineer"])

    if s.check() != sat:
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Helper to invert mapping: house -> value for a category
    def house_to_value(var_map, values):
        inv = {}
        for val in values:
            pos = m.evaluate(var_map[val]).as_long()
            inv[pos] = val
        return inv

    names_by_house = house_to_value(name_vars, Names)
    cars_by_house = house_to_value(car_vars, CarModels)
    styles_by_house = house_to_value(style_vars, HouseStyles)
    pets_by_house = house_to_value(pet_vars, Pets)
    occs_by_house = house_to_value(occ_vars, Occupations)
    vacs_by_house = house_to_value(vac_vars, Vacations)

    header = ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            names_by_house[h],
            cars_by_house[h],
            styles_by_house[h],
            pets_by_house[h],
            occs_by_house[h],
            vacs_by_house[h],
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()