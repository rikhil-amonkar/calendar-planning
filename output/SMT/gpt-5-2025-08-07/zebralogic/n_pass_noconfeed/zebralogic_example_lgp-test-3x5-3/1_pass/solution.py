import json
from z3 import Solver, Int, Distinct, And, Or, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3]

    # Define categories and items
    Names = ["Eric", "Peter", "Arnold"]
    Smoothies = ["cherry", "watermelon", "desert"]
    Flowers = ["carnations", "lilies", "daffodils"]
    Animals = ["cat", "horse", "bird"]
    Hobbies = ["photography", "cooking", "gardening"]

    # Create Z3 integer variables for each item in each category representing the house number (1..3)
    def create_vars(prefix, items):
        return {item: Int(f"{prefix}_{item}") for item in items}

    name_vars = create_vars("Name", Names)
    smoothie_vars = create_vars("Smoothie", Smoothies)
    flower_vars = create_vars("Flower", Flowers)
    animal_vars = create_vars("Animal", Animals)
    hobby_vars = create_vars("Hobby", Hobbies)

    s = Solver()

    # Domain constraints: all items must be in houses 1..3
    for vars_dict in [name_vars, smoothie_vars, flower_vars, animal_vars, hobby_vars]:
        for v in vars_dict.values():
            s.add(And(v >= 1, v <= 3))
        s.add(Distinct(list(vars_dict.values())))

    # Shorthand accessors
    pos = {
        "Eric": name_vars["Eric"],
        "Peter": name_vars["Peter"],
        "Arnold": name_vars["Arnold"],
        "cherry": smoothie_vars["cherry"],
        "watermelon": smoothie_vars["watermelon"],
        "desert": smoothie_vars["desert"],
        "carnations": flower_vars["carnations"],
        "lilies": flower_vars["lilies"],
        "daffodils": flower_vars["daffodils"],
        "cat": animal_vars["cat"],
        "horse": animal_vars["horse"],
        "bird": animal_vars["bird"],
        "photography": hobby_vars["photography"],
        "cooking": hobby_vars["cooking"],
        "gardening": hobby_vars["gardening"],
    }

    # Clues as constraints:
    # 1. The person who keeps horses and the photography enthusiast are next to each other.
    s.add(Abs(pos["horse"] - pos["photography"]) == 1)

    # 2. The bird keeper is the person who likes Cherry smoothies.
    s.add(pos["bird"] == pos["cherry"])

    # 3. The person who loves cooking is the Desert smoothie lover.
    s.add(pos["cooking"] == pos["desert"])

    # 4. The person who enjoys gardening is the person who loves a carnations arrangement.
    s.add(pos["gardening"] == pos["carnations"])

    # 5. The person who loves cooking is directly left of Peter.
    s.add(pos["cooking"] + 1 == pos["Peter"])

    # 6. The person who loves a bouquet of daffodils is the Desert smoothie lover.
    s.add(pos["daffodils"] == pos["desert"])

    # 7. The Watermelon smoothie lover is the person who keeps horses.
    s.add(pos["watermelon"] == pos["horse"])

    # 8. The photography enthusiast is Eric.
    s.add(pos["photography"] == pos["Eric"])

    # Solve
    if s.check() != sat:
        raise ValueError("No solution found for the given puzzle.")

    m = s.model()

    # Build reverse lookup for each category: house -> value
    def invert(vars_dict):
        inv = {}
        for k, v in vars_dict.items():
            inv[m[v].as_long()] = k
        return inv

    name_by_house = invert(name_vars)
    smoothie_by_house = invert(smoothie_vars)
    flower_by_house = invert(flower_vars)
    animal_by_house = invert(animal_vars)
    hobby_by_house = invert(hobby_vars)

    # Prepare JSON output
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            name_by_house[h],
            smoothie_by_house[h],
            flower_by_house[h],
            animal_by_house[h],
            hobby_by_house[h]
        ]
        solution["solution"]["rows"].append(row)

    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))