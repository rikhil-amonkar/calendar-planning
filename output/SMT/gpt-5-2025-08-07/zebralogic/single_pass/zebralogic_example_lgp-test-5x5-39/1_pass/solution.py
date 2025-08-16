from z3 import Solver, Int, Distinct, And, sat
import json

def solve_puzzle():
    houses = range(1, 6)

    # Categories and values
    Names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    Birthdays = ["mar", "april", "sept", "feb", "jan"]
    Mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    Occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    HairColors = ["red", "blonde", "black", "gray", "brown"]

    # Create Z3 variables representing the house position (1..5) of each attribute value
    name_vars = {n: Int(f"name_{n}") for n in Names}
    bday_vars = {b: Int(f"bday_{b}") for b in Birthdays}
    mother_vars = {m: Int(f"mother_{m}") for m in Mothers}
    job_vars = {j: Int(f"job_{j}") for j in Occupations}
    hair_vars = {h: Int(f"hair_{h}") for h in HairColors}

    s = Solver()

    # Domain constraints
    for var_dict in [name_vars, bday_vars, mother_vars, job_vars, hair_vars]:
        for v in var_dict.values():
            s.add(And(v >= 1, v <= 5))

    # All-different within each category
    s.add(Distinct([name_vars[n] for n in Names]))
    s.add(Distinct([bday_vars[b] for b in Birthdays]))
    s.add(Distinct([mother_vars[m] for m in Mothers]))
    s.add(Distinct([job_vars[j] for j in Occupations]))
    s.add(Distinct([hair_vars[h] for h in HairColors]))

    # Clues
    # 1. The person whose birthday is in March is in the fifth house.
    s.add(bday_vars["mar"] == 5)

    # 2. The person whose birthday is in February is in the first house.
    s.add(bday_vars["feb"] == 1)

    # 3. The person who is a doctor is Eric.
    s.add(job_vars["doctor"] == name_vars["Eric"])

    # 4. The person whose mother's name is Janelle is in the third house.
    s.add(mother_vars["Janelle"] == 3)

    # 5. The person who is an artist is the person who has brown hair.
    s.add(job_vars["artist"] == hair_vars["brown"])

    # 6. The person who is an artist is in the fourth house.
    s.add(job_vars["artist"] == 4)

    # 7. The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    s.add(mother_vars["Penny"] < hair_vars["black"])

    # 8. Peter is the person who has black hair.
    s.add(name_vars["Peter"] == hair_vars["black"])

    # 9. The person who has gray hair is the person who is a teacher.
    s.add(hair_vars["gray"] == job_vars["teacher"])

    # 10. Alice is The person whose mother's name is Kailyn.
    s.add(name_vars["Alice"] == mother_vars["Kailyn"])

    # 11. Arnold is somewhere to the right of the person whose birthday is in September.
    s.add(name_vars["Arnold"] > bday_vars["sept"])

    # 12. The person who has brown hair is the person whose birthday is in January.
    s.add(hair_vars["brown"] == bday_vars["jan"])

    # 13. Arnold is the person who has blonde hair.
    s.add(name_vars["Arnold"] == hair_vars["blonde"])

    # 14. The person whose mother's name is Holly is the person who has black hair.
    s.add(mother_vars["Holly"] == hair_vars["black"])

    # 15. Peter is the person who is a lawyer.
    s.add(name_vars["Peter"] == job_vars["lawyer"])

    # 16. The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
    s.add(bday_vars["sept"] < mother_vars["Kailyn"])

    # 17. Alice is the person who has gray hair.
    s.add(name_vars["Alice"] == hair_vars["gray"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Invert mappings: for each house, find the label for each category
    def invert(var_dict):
        inv = {}
        for label, var in var_dict.items():
            inv[m[var].as_long()] = label
        return inv

    inv_name = invert(name_vars)
    inv_bday = invert(bday_vars)
    inv_mother = invert(mother_vars)
    inv_job = invert(job_vars)
    inv_hair = invert(hair_vars)

    rows = []
    for house in range(1, 6):
        rows.append([
            str(house),
            inv_name[house],
            inv_bday[house],
            inv_mother[house],
            inv_job[house],
            inv_hair[house],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))