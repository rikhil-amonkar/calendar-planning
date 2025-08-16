import json
from z3 import Int, Solver, Distinct, Or, And

def solve_puzzle():
    # Houses are numbered 1..3 from left to right
    houses = [1, 2, 3]

    # Attribute values
    Names = ["Eric", "Peter", "Arnold"]
    Smoothies = ["cherry", "watermelon", "desert"]
    Flowers = ["carnations", "lilies", "daffodils"]
    Animals = ["cat", "horse", "bird"]
    Hobbies = ["photography", "cooking", "gardening"]

    # Create Z3 variables: each attribute value has a house number (1..3)
    name_vars = {n: Int(f"Name_{n}") for n in Names}
    smoothie_vars = {s: Int(f"Smoothie_{s}") for s in Smoothies}
    flower_vars = {f: Int(f"Flower_{f}") for f in Flowers}
    animal_vars = {a: Int(f"Animal_{a}") for a in Animals}
    hobby_vars = {h: Int(f"Hobby_{h}") for h in Hobbies}

    # Helper: constrain vars to be within 1..3 and all-different within each category
    def in_range(vars_dict):
        return [And(v >= 1, v <= 3) for v in vars_dict.values()]

    def all_diff(vars_dict):
        return [Distinct(list(vars_dict.values()))]

    s = Solver()

    # Domain constraints
    s.add(*in_range(name_vars))
    s.add(*in_range(smoothie_vars))
    s.add(*in_range(flower_vars))
    s.add(*in_range(animal_vars))
    s.add(*in_range(hobby_vars))

    # Uniqueness constraints
    s.add(*all_diff(name_vars))
    s.add(*all_diff(smoothie_vars))
    s.add(*all_diff(flower_vars))
    s.add(*all_diff(animal_vars))
    s.add(*all_diff(hobby_vars))

    # Clues:
    # 1. Horses and the photography enthusiast are next to each other.
    s.add(Or(
        animal_vars["horse"] - hobby_vars["photography"] == 1,
        animal_vars["horse"] - hobby_vars["photography"] == -1
    ))

    # 2. The bird keeper is the person who likes Cherry smoothies.
    s.add(animal_vars["bird"] == smoothie_vars["cherry"])

    # 3. The person who loves cooking is the Desert smoothie lover.
    s.add(hobby_vars["cooking"] == smoothie_vars["desert"])

    # 4. Gardening equals carnations.
    s.add(hobby_vars["gardening"] == flower_vars["carnations"])

    # 5. Cooking is directly left of Peter.
    s.add(hobby_vars["cooking"] + 1 == name_vars["Peter"])

    # 6. Daffodils equals Desert smoothie lover.
    s.add(flower_vars["daffodils"] == smoothie_vars["desert"])

    # 7. Watermelon smoothie lover keeps horses.
    s.add(smoothie_vars["watermelon"] == animal_vars["horse"])

    # 8. The photography enthusiast is Eric.
    s.add(hobby_vars["photography"] == name_vars["Eric"])

    if s.check() != 0:  # sat
        m = s.model()

        # Build inverse mapping: for each house, find the value of each category
        def invert(vars_dict):
            inv = {}
            for k, v in vars_dict.items():
                inv[m[v].as_long()] = k
            return inv

        inv_names = invert(name_vars)
        inv_smoothies = invert(smoothie_vars)
        inv_flowers = invert(flower_vars)
        inv_animals = invert(animal_vars)
        inv_hobbies = invert(hobby_vars)

        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }

        for h in houses:
            row = [
                str(h),
                inv_names[h],
                inv_smoothies[h],
                inv_flowers[h],
                inv_animals[h],
                inv_hobbies[h]
            ]
            result["solution"]["rows"].append(row)

        print(json.dumps(result, ensure_ascii=False))
    else:
        # No solution (shouldn't happen with given clues)
        print(json.dumps({
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()