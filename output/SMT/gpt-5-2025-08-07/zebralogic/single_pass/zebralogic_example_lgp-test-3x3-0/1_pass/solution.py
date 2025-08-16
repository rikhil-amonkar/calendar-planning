import json
from z3 import Solver, Int, And, Or, Distinct, sat

def main():
    houses = [1, 2, 3]

    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    def var_label(label):
        return label.replace(" ", "_")

    name_pos = {n: Int(f"house_of_{var_label(n)}") for n in names}
    edu_pos = {e: Int(f"house_of_{var_label(e)}") for e in educations}
    occ_pos = {o: Int(f"house_of_{var_label(o)}") for o in occupations}

    s = Solver()

    # Domains and uniqueness within each category
    for d in (name_pos, edu_pos, occ_pos):
        vars_list = list(d.values())
        for v in vars_list:
            s.add(And(v >= 1, v <= 3))
        s.add(Distinct(vars_list))

    # Clues:
    # 1. Teacher is directly left of the person with an associate's degree.
    s.add(occ_pos["teacher"] + 1 == edu_pos["associate"])

    # 2. The person with an associate's degree and Eric are next to each other.
    s.add(Or(edu_pos["associate"] == name_pos["Eric"] + 1,
             edu_pos["associate"] == name_pos["Eric"] - 1))

    # 3. Peter is the person with a high school diploma.
    s.add(name_pos["Peter"] == edu_pos["high school"])

    # 4. The person who is a doctor is the person with a bachelor's degree.
    s.add(occ_pos["doctor"] == edu_pos["bachelor"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for h in houses:
        name = next(n for n, v in name_pos.items() if m.eval(v).as_long() == h)
        edu = next(e for e, v in edu_pos.items() if m.eval(v).as_long() == h)
        occ = next(o for o, v in occ_pos.items() if m.eval(v).as_long() == h)
        rows.append([str(h), name, edu, occ])

    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(solution))

if __name__ == "__main__":
    main()