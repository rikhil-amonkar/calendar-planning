import json
from z3 import Int, Solver, Distinct, And, Or, If

def main():
    houses = [1, 2, 3, 4, 5]

    # Domains
    Names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    Birthdays = ["mar", "april", "sept", "feb", "jan"]
    Mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    Occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    HairColors = ["red", "blonde", "black", "gray", "brown"]

    # Helper to create position variables for each category
    def mk_vars(prefix, items):
        return {item: Int(f"{prefix}_{item}") for item in items}

    name_pos = mk_vars("name", Names)
    bday_pos = mk_vars("bday", Birthdays)
    mother_pos = mk_vars("mother", Mothers)
    job_pos = mk_vars("job", Occupations)
    hair_pos = mk_vars("hair", HairColors)

    s = Solver()

    # All variables in range 1..5
    for d in [name_pos, bday_pos, mother_pos, job_pos, hair_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # All-different for each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([bday_pos[m] for m in Birthdays]))
    s.add(Distinct([mother_pos[m] for m in Mothers]))
    s.add(Distinct([job_pos[j] for j in Occupations]))
    s.add(Distinct([hair_pos[h] for h in HairColors]))

    # Clues:
    # 1. March in fifth house.
    s.add(bday_pos["mar"] == 5)
    # 2. February in first house.
    s.add(bday_pos["feb"] == 1)
    # 3. Doctor is Eric.
    s.add(job_pos["doctor"] == name_pos["Eric"])
    # 4. Janelle in third house.
    s.add(mother_pos["Janelle"] == 3)
    # 5. Artist is brown hair.
    s.add(job_pos["artist"] == hair_pos["brown"])
    # 6. Artist in fourth house.
    s.add(job_pos["artist"] == 4)
    # 7. Penny is somewhere to the left of the person who has black hair.
    s.add(mother_pos["Penny"] < hair_pos["black"])
    # 8. Peter is the person who has black hair.
    s.add(name_pos["Peter"] == hair_pos["black"])
    # 9. Gray hair is the person who is a teacher.
    s.add(hair_pos["gray"] == job_pos["teacher"])
    # 10. Alice is The person whose mother's name is Kailyn.
    s.add(name_pos["Alice"] == mother_pos["Kailyn"])
    # 11. Arnold is somewhere to the right of the person whose birthday is in September.
    s.add(name_pos["Arnold"] > bday_pos["sept"])
    # 12. The person who has brown hair is the person whose birthday is in January.
    s.add(hair_pos["brown"] == bday_pos["jan"])
    # 13. Arnold is the person who has blonde hair.
    s.add(name_pos["Arnold"] == hair_pos["blonde"])
    # 14. The person whose mother's name is Holly is the person who has black hair.
    s.add(mother_pos["Holly"] == hair_pos["black"])
    # 15. Peter is the person who is a lawyer.
    s.add(name_pos["Peter"] == job_pos["lawyer"])
    # 16. The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
    s.add(bday_pos["sept"] < mother_pos["Kailyn"])
    # 17. Alice is the person who has gray hair.
    s.add(name_pos["Alice"] == hair_pos["gray"])

    if s.check() != 1:  # 1 == sat
        print(json.dumps({"solution": {"header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"], "rows": []}}))
        return

    m = s.model()

    # Invert mappings: for each house, find which value sits there for each category
    def invert(pos_map, domain):
        inv = {i: None for i in houses}
        for item in domain:
            inv[m[pos_map[item]].as_long()] = item
        return inv

    inv_name = invert(name_pos, Names)
    inv_bday = invert(bday_pos, Birthdays)
    inv_mother = invert(mother_pos, Mothers)
    inv_job = invert(job_pos, Occupations)
    inv_hair = invert(hair_pos, HairColors)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            inv_name[h],
            inv_bday[h],
            inv_mother[h],
            inv_job[h],
            inv_hair[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()