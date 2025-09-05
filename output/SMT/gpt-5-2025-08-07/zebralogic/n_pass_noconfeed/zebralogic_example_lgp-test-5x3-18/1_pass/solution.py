import json
from z3 import Solver, Int, Distinct, And, Or

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    Names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    Flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    Animals = ["dog", "horse", "cat", "bird", "fish"]

    # Z3 variables: position (house index) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    flower_pos = {f: Int(f"flower_{f}") for f in Flowers}
    animal_pos = {a: Int(f"animal_{a}") for a in Animals}

    s = Solver()

    # Domains: each attribute occurs in exactly one house (1..5), and all are distinct within category
    for v in name_pos.values():
        s.add(And(v >= 1, v <= 5))
    for v in flower_pos.values():
        s.add(And(v >= 1, v <= 5))
    for v in animal_pos.values():
        s.add(And(v >= 1, v <= 5))

    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([flower_pos[f] for f in Flowers]))
    s.add(Distinct([animal_pos[a] for a in Animals]))

    # Helper lambdas
    exactly_left_of = lambda x, y: x + 1 == y

    # Clues
    # 1. Alice is in the second house.
    s.add(name_pos["Alice"] == 2)

    # 2. The person who loves the bouquet of lilies is the bird keeper.
    s.add(flower_pos["lilies"] == animal_pos["bird"])

    # 3. Peter is somewhere to the right of the person who loves the vase of tulips.
    s.add(name_pos["Peter"] > flower_pos["tulips"])

    # 4. The fish enthusiast is the person who loves a bouquet of daffodils.
    s.add(animal_pos["fish"] == flower_pos["daffodils"])

    # 5. The person who keeps horses is Eric.
    s.add(animal_pos["horse"] == name_pos["Eric"])

    # 6. There are two houses between the dog owner and Bob. (diff == 3)
    s.add(Or(animal_pos["dog"] == name_pos["Bob"] + 3,
             name_pos["Bob"] == animal_pos["dog"] + 3))

    # 7. The fish enthusiast is directly left of Bob.
    s.add(exactly_left_of(animal_pos["fish"], name_pos["Bob"]))

    # 8. Alice is directly left of the person who keeps horses.
    s.add(exactly_left_of(name_pos["Alice"], animal_pos["horse"]))

    # 9. The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
    s.add(exactly_left_of(flower_pos["carnations"], flower_pos["tulips"]))

    # 10. The cat lover is not in the first house.
    s.add(animal_pos["cat"] != 1)

    # Solve
    if s.check() != 1:  # sat
        raise RuntimeError("No solution found by the SMT solver.")

    m = s.model()

    # Build the solution table by house
    # Invert mappings to get attribute by house
    house_to_name = {}
    for n in Names:
        house_to_name[m[name_pos[n]].as_long()] = n

    house_to_flower = {}
    for f in Flowers:
        house_to_flower[m[flower_pos[f]].as_long()] = f

    house_to_animal = {}
    for a in Animals:
        house_to_animal[m[animal_pos[a]].as_long()] = a

    rows = []
    for h in houses:
        rows.append([str(h),
                     house_to_name[h],
                     house_to_flower[h],
                     house_to_animal[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))