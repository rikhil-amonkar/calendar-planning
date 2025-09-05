import json
from z3 import Solver, Int, Distinct, And, Or

def solve_puzzle():
    houses = [1, 2, 3]

    # Define categories and their items
    Names = ["Arnold", "Peter", "Eric"]
    Animals = ["bird", "horse", "cat"]
    Birthdays = ["jan", "sept", "april"]
    Hobbies = ["photography", "cooking", "gardening"]
    Drinks = ["milk", "water", "tea"]
    HairColors = ["black", "brown", "blonde"]

    # Create Z3 Int variables for each item representing the house number (1..3) it is in
    name_vars = {n: Int(n) for n in Names}
    animal_vars = {a: Int(a) for a in Animals}
    birthday_vars = {b: Int(b) for b in Birthdays}
    hobby_vars = {h: Int(h) for h in Hobbies}
    drink_vars = {d: Int(d) for d in Drinks}
    hair_vars = {c: Int(c) for c in HairColors}

    s = Solver()

    # Domain constraints: each item must be in one of the houses 1..3
    for var_dict in [name_vars, animal_vars, birthday_vars, hobby_vars, drink_vars, hair_vars]:
        for v in var_dict.values():
            s.add(And(v >= 1, v <= 3))

    # All-different constraints within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*animal_vars.values()))
    s.add(Distinct(*birthday_vars.values()))
    s.add(Distinct(*hobby_vars.values()))
    s.add(Distinct(*drink_vars.values()))
    s.add(Distinct(*hair_vars.values()))

    # Clues:
    # 1. The person who has brown hair is the person who loves cooking.
    s.add(hair_vars["brown"] == hobby_vars["cooking"])

    # 2. The person whose birthday is in April is in the third house.
    s.add(birthday_vars["april"] == 3)

    # 3. Eric is not in the first house.
    s.add(name_vars["Eric"] != 1)

    # 4. The cat lover is in the second house.
    s.add(animal_vars["cat"] == 2)

    # 5. The person who has blonde hair is somewhere to the left of the person who likes milk.
    s.add(hair_vars["blonde"] < drink_vars["milk"])

    # 6. The person who enjoys gardening is the person who likes milk.
    s.add(hobby_vars["gardening"] == drink_vars["milk"])

    # 7. The cat lover is the person who has brown hair.
    s.add(animal_vars["cat"] == hair_vars["brown"])

    # 8. Arnold is the bird keeper.
    s.add(name_vars["Arnold"] == animal_vars["bird"])

    # 9. The one who only drinks water is the photography enthusiast.
    s.add(drink_vars["water"] == hobby_vars["photography"])

    # 10. The person whose birthday is in September is directly left of Arnold.
    s.add(birthday_vars["sept"] + 1 == name_vars["Arnold"])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("Puzzle has no solution or is not satisfiable")

    m = s.model()

    def value_to_key(var_dict, house):
        for k, v in var_dict.items():
            if m[v].as_long() == house:
                return k
        return None

    rows = []
    for house in houses:
        name = value_to_key(name_vars, house)
        animal = value_to_key(animal_vars, house)
        birthday = value_to_key(birthday_vars, house)
        hobby = value_to_key(hobby_vars, house)
        drink = value_to_key(drink_vars, house)
        hair = value_to_key(hair_vars, house)
        rows.append([str(house), name, animal, birthday, hobby, drink, hair])

    result = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution))