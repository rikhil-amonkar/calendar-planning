import json
from z3 import Solver, Ints, And, Or, Distinct, Implies

def solve():
    # Indices for attributes
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occs = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    N = {n: i for i, n in enumerate(names)}
    O = {o: i for i, o in enumerate(occs)}
    C = {c: i for i, c in enumerate(cars)}

    # Variables: for each house 0..5 (representing houses 1..6)
    name = [Ints(f"name_{i}")[0] for i in range(6)]
    occ  = [Ints(f"occ_{i}")[0] for i in range(6)]
    car  = [Ints(f"car_{i}")[0] for i in range(6)]

    s = Solver()

    # Domains
    for i in range(6):
        s.add(And(name[i] >= 0, name[i] <= 5))
        s.add(And(occ[i]  >= 0, occ[i]  <= 5))
        s.add(And(car[i]  >= 0, car[i]  <= 5))

    # All different across houses
    s.add(Distinct(name))
    s.add(Distinct(occ))
    s.add(Distinct(car))

    # Clues:

    # 1. Ford F-150 in the fifth house (index 4)
    s.add(car[4] == C["ford f150"])

    # 2. Chevrolet Silverado not in the second house (index 1)
    s.add(car[1] != C["chevrolet silverado"])

    # 3. Honda Civic owner and Peter are next to each other
    for h in range(6):
        neighbors = []
        if h > 0:
            neighbors.append(name[h-1] == N["Peter"])
        if h < 5:
            neighbors.append(name[h+1] == N["Peter"])
        s.add(Implies(car[h] == C["honda civic"], Or(neighbors)))

    # 4. Lawyer not in the fifth house
    s.add(occ[4] != O["lawyer"])

    # 5. Nurse is directly left of artist
    for h in range(6):
        s.add(Implies(occ[h] == O["nurse"], And(h < 5, occ[h+1] == O["artist"])))

    # 6. Carol is somewhere to the right of Eric
    right_pairs = []
    for i in range(6):
        for j in range(i+1, 6):
            right_pairs.append(And(name[i] == N["Eric"], name[j] == N["Carol"]))
    s.add(Or(right_pairs))

    # 7. The person who is a doctor is Eric
    for h in range(6):
        s.add((occ[h] == O["doctor"]) == (name[h] == N["Eric"]))

    # 8. Teacher is somewhere to the left of nurse
    left_pairs = []
    for i in range(6):
        for j in range(i+1, 6):
            left_pairs.append(And(occ[i] == O["teacher"], occ[j] == O["nurse"]))
    s.add(Or(left_pairs))

    # 9. Carol is not in the sixth house (index 5)
    s.add(name[5] != N["Carol"])

    # 10. Engineer is Bob
    for h in range(6):
        s.add((occ[h] == O["engineer"]) == (name[h] == N["Bob"]))

    # 11. Toyota Camry owner is the nurse
    for h in range(6):
        s.add((car[h] == C["toyota camry"]) == (occ[h] == O["nurse"]))

    # 12. One house between Peter and the lawyer (distance 2)
    for h in range(6):
        opts = []
        if h >= 2:
            opts.append(occ[h-2] == O["lawyer"])
        if h <= 3:
            opts.append(occ[h+2] == O["lawyer"])
        s.add(Implies(name[h] == N["Peter"], Or(opts)))

    # 13. One house between the Tesla Model 3 owner and Bob (distance 2)
    for h in range(6):
        opts = []
        if h >= 2:
            opts.append(name[h-2] == N["Bob"])
        if h <= 3:
            opts.append(name[h+2] == N["Bob"])
        s.add(Implies(car[h] == C["tesla model 3"], Or(opts)))

    # 14. Arnold is the artist
    for h in range(6):
        s.add((name[h] == N["Arnold"]) == (occ[h] == O["artist"]))

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build output rows
    rows = []
    for i in range(6):
        house_num = str(i+1)
        name_str = names[m[name[i]].as_long()]
        occ_str = occs[m[occ[i]].as_long()]
        car_str = cars[m[car[i]].as_long()]
        rows.append([house_num, name_str, occ_str, car_str])

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve()