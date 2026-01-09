import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = list(range(1, 7))

    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    def name_var(n): return f"Name_{n}"
    def occ_var(o): return f"Occ_{o.replace(' ', '_')}"
    def car_var(c): return f"Car_{c.replace(' ', '_')}"

    prob = Problem()

    # Add variables with domains
    for n in names:
        prob.addVariable(name_var(n), houses)
    for o in occupations:
        prob.addVariable(occ_var(o), houses)
    for c in cars:
        prob.addVariable(car_var(c), houses)

    # All-different constraints per category
    prob.addConstraint(AllDifferentConstraint(), [name_var(n) for n in names])
    prob.addConstraint(AllDifferentConstraint(), [occ_var(o) for o in occupations])
    prob.addConstraint(AllDifferentConstraint(), [car_var(c) for c in cars])

    # Clues:
    # 1. Ford F-150 is in the fifth house.
    prob.addConstraint(lambda x: x == 5, [car_var("ford f150")])

    # 2. Chevrolet Silverado not in the second house.
    prob.addConstraint(lambda x: x != 2, [car_var("chevrolet silverado")])

    # 3. Honda Civic owner and Peter are next to each other.
    prob.addConstraint(lambda h, p: abs(h - p) == 1, [car_var("honda civic"), name_var("Peter")])

    # 4. Lawyer not in the fifth house.
    prob.addConstraint(lambda x: x != 5, [occ_var("lawyer")])

    # 5. Nurse is directly left of artist.
    prob.addConstraint(lambda n, a: n == a - 1, [occ_var("nurse"), occ_var("artist")])

    # 6. Carol is somewhere to the right of Eric.
    prob.addConstraint(lambda c, e: c > e, [name_var("Carol"), name_var("Eric")])

    # 7. Doctor is Eric.
    prob.addConstraint(lambda d, e: d == e, [occ_var("doctor"), name_var("Eric")])

    # 8. Teacher is somewhere to the left of nurse.
    prob.addConstraint(lambda t, n: t < n, [occ_var("teacher"), occ_var("nurse")])

    # 9. Carol is not in the sixth house.
    prob.addConstraint(lambda c: c != 6, [name_var("Carol")])

    # 10. Engineer is Bob.
    prob.addConstraint(lambda eng, bob: eng == bob, [occ_var("engineer"), name_var("Bob")])

    # 11. Toyota Camry owner is the nurse.
    prob.addConstraint(lambda camry, nurse: camry == nurse, [car_var("toyota camry"), occ_var("nurse")])

    # 12. One house between Peter and the lawyer.
    prob.addConstraint(lambda p, l: abs(p - l) == 2, [name_var("Peter"), occ_var("lawyer")])

    # 13. One house between Tesla Model 3 and Bob.
    prob.addConstraint(lambda tesla, bob: abs(tesla - bob) == 2, [car_var("tesla model 3"), name_var("Bob")])

    # 14. Arnold is the artist.
    prob.addConstraint(lambda artist, arnold: artist == arnold, [occ_var("artist"), name_var("Arnold")])

    solutions = prob.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build lookup maps from positions to attribute values
    name_pos = {n: sol[name_var(n)] for n in names}
    occ_pos = {o: sol[occ_var(o)] for o in occupations}
    car_pos = {c: sol[car_var(c)] for c in cars}

    pos_to_name = {pos: n for n, pos in name_pos.items()}
    pos_to_occ = {pos: o for o, pos in occ_pos.items()}
    pos_to_car = {pos: c for c, pos in car_pos.items()}

    rows = []
    for h in houses:
        rows.append([
            str(h),
            pos_to_name[h],
            pos_to_occ[h],
            pos_to_car[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()