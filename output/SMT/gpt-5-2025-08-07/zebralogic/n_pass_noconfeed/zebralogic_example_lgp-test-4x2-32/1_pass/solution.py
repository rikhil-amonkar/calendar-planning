import json
from z3 import Int, Solver, Distinct, And, Or, Abs, sat

def main():
    houses = [1, 2, 3, 4]

    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    # Variables: position (house number) for each name and each pet
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_pet = {p: Int(f"pos_pet_{p}") for p in pets}

    s = Solver()

    # Domains: all positions are between 1 and 4
    for v in list(pos_name.values()) + list(pos_pet.values()):
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within categories
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_pet[p] for p in pets]))

    # Clues:
    # 1. The person who owns a dog is somewhere to the right of Alice.
    s.add(pos_pet["dog"] > pos_name["Alice"])

    # 2. Eric is not in the first house.
    s.add(pos_name["Eric"] != 1)

    # 3. Eric is the person who keeps a pet bird.
    s.add(pos_name["Eric"] == pos_pet["bird"])

    # 4. There is one house between the person with an aquarium of fish and Peter.
    s.add(Abs(pos_pet["fish"] - pos_name["Peter"]) == 2)

    # 5. Alice is not in the first house.
    s.add(pos_name["Alice"] != 1)

    # 6. Arnold is the person with an aquarium of fish.
    s.add(pos_name["Arnold"] == pos_pet["fish"])

    if s.check() != sat:
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Invert mappings to get per-house assignments
    house_to_name = {}
    for n in names:
        house_to_name[m[pos_name[n]].as_long()] = n

    house_to_pet = {}
    for p in pets:
        house_to_pet[m[pos_pet[p]].as_long()] = p

    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": []
        }
    }

    for h in houses:
        result["solution"]["rows"].append([str(h), house_to_name[h], house_to_pet[h]])

    print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))

if __name__ == "__main__":
    main()