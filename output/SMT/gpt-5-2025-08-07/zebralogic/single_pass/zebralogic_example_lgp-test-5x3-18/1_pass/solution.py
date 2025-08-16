import json
from z3 import Solver, Int, Distinct, And, Abs, sat

def solve_puzzle():
    houses = range(1, 6)

    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # Position variables: for each attribute value, the house index (1..5) where it appears
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_flower = {f: Int(f"pos_flower_{f}") for f in flowers}
    pos_animal = {a: Int(f"pos_animal_{a}") for a in animals}

    s = Solver()

    # Domains: each position is between 1 and 5
    for d in [pos_name, pos_flower, pos_animal]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # Each category is a permutation of 1..5 (all different positions)
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_flower.values()))
    s.add(Distinct(*pos_animal.values()))

    # Clues:
    # 1. Alice is in the second house.
    s.add(pos_name["Alice"] == 2)

    # 2. Lilies <-> Bird
    s.add(pos_flower["lilies"] == pos_animal["bird"])

    # 3. Peter is somewhere to the right of the person who loves the vase of tulips.
    s.add(pos_name["Peter"] > pos_flower["tulips"])

    # 4. Fish <-> Daffodils
    s.add(pos_animal["fish"] == pos_flower["daffodils"])

    # 5. The person who keeps horses is Eric.
    s.add(pos_animal["horse"] == pos_name["Eric"])

    # 6. There are two houses between the dog owner and Bob. (distance 3)
    s.add(Abs(pos_animal["dog"] - pos_name["Bob"]) == 3)

    # 7. The fish enthusiast is directly left of Bob.
    s.add(pos_animal["fish"] == pos_name["Bob"] - 1)

    # 8. Alice is directly left of the person who keeps horses.
    s.add(pos_name["Alice"] + 1 == pos_animal["horse"])

    # 9. Carnations is directly left of Tulips.
    s.add(pos_flower["carnations"] + 1 == pos_flower["tulips"])

    # 10. The cat lover is not in the first house.
    s.add(pos_animal["cat"] != 1)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Evaluate positions
    pos_name_eval = {k: m.evaluate(v).as_long() for k, v in pos_name.items()}
    pos_flower_eval = {k: m.evaluate(v).as_long() for k, v in pos_flower.items()}
    pos_animal_eval = {k: m.evaluate(v).as_long() for k, v in pos_animal.items()}

    # Invert to get attribute by house
    def value_at_house(pos_map, house):
        for k, v in pos_map.items():
            if v == house:
                return k
        return None

    rows = []
    for h in houses:
        rows.append([
            str(h),
            value_at_house(pos_name_eval, h),
            value_at_house(pos_flower_eval, h),
            value_at_house(pos_animal_eval, h),
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()