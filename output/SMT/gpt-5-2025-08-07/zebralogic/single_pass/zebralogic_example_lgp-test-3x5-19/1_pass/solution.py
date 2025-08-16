import json
from z3 import Solver, Int, Distinct, Or, And, sat

def solve_puzzle():
    # Indices for values
    ARNOLD, PETER, ERIC = 0, 1, 2
    DOCTOR, TEACHER, ENGINEER = 0, 1, 2
    ASSOCIATE, HIGH_SCHOOL, BACHELOR = 0, 1, 2
    DESERT, CHERRY, WATERMELON = 0, 1, 2
    GARDENING, COOKING, PHOTOGRAPHY = 0, 1, 2

    names_vals = ["Arnold", "Peter", "Eric"]
    occupations_vals = ["doctor", "teacher", "engineer"]
    educations_vals = ["associate", "high school", "bachelor"]
    smoothies_vals = ["desert", "cherry", "watermelon"]
    hobbies_vals = ["gardening", "cooking", "photography"]

    houses = range(3)  # 0->House 1, 1->House 2, 2->House 3

    # Variables: for each house, an Int representing the index of the attribute value
    name = [Int(f"name_{h}") for h in houses]
    occupation = [Int(f"occupation_{h}") for h in houses]
    education = [Int(f"education_{h}") for h in houses]
    smoothie = [Int(f"smoothie_{h}") for h in houses]
    hobby = [Int(f"hobby_{h}") for h in houses]

    s = Solver()

    # Domains: each variable in 0..2
    for arr in [name, occupation, education, smoothie, hobby]:
        for v in arr:
            s.add(v >= 0, v <= 2)

    # All-different across houses for each attribute category
    s.add(Distinct(name))
    s.add(Distinct(occupation))
    s.add(Distinct(education))
    s.add(Distinct(smoothie))
    s.add(Distinct(hobby))

    # Clues encoding

    # 1. The Desert smoothie lover is the person who is a doctor.
    s.add(Or([And(smoothie[h] == DESERT, occupation[h] == DOCTOR) for h in houses]))

    # 2. Arnold is not in the third house.
    s.add(name[2] != ARNOLD)

    # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
    s.add(Or([And(name[hP] == PETER, smoothie[hC] == CHERRY, hC > hP)
              for hP in houses for hC in houses]))

    # 4. The person who loves cooking is in the second house.
    s.add(hobby[1] == COOKING)

    # 5. The person who loves cooking is Peter.
    s.add(Or([And(hobby[h] == COOKING, name[h] == PETER) for h in houses]))

    # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    s.add(Or([And(education[hA] == ASSOCIATE, hobby[hG] == GARDENING, hA > hG)
              for hA in houses for hG in houses]))

    # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    s.add(Or([And(education[hB] == BACHELOR, smoothie[hD] == DESERT, hB > hD)
              for hB in houses for hD in houses]))

    # 8. The person who loves cooking is the person who is a doctor.
    s.add(Or([And(hobby[h] == COOKING, occupation[h] == DOCTOR) for h in houses]))

    # 9. The photography enthusiast is the person who is a teacher.
    s.add(Or([And(hobby[h] == PHOTOGRAPHY, occupation[h] == TEACHER) for h in houses]))

    assert s.check() == sat, "Puzzle has no solution"
    m = s.model()

    rows = []
    for h in houses:
        row = [
            str(h + 1),
            names_vals[m[name[h]].as_long()],
            occupations_vals[m[occupation[h]].as_long()],
            educations_vals[m[education[h]].as_long()],
            smoothies_vals[m[smoothie[h]].as_long()],
            hobbies_vals[m[hobby[h]].as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution))