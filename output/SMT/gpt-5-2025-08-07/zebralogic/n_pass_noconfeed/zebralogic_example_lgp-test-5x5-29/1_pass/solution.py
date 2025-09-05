import json
from z3 import *

def main():
    # Define domains
    houses = [1, 2, 3, 4, 5]

    Names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    Nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    Vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    Educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    Occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

    # Create Z3 variables for each attribute -> house position
    def mk_vars(prefix, items):
        return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

    name_pos = mk_vars("Name", Names)
    nat_pos = mk_vars("Nat", Nationalities)
    vac_pos = mk_vars("Vac", Vacations)
    edu_pos = mk_vars("Edu", Educations)
    occ_pos = mk_vars("Occ", Occupations)

    s = Solver()

    # Domain constraints: each position is between 1 and 5
    for group in [name_pos, nat_pos, vac_pos, edu_pos, occ_pos]:
        for v in group.values():
            s.add(And(v >= 1, v <= 5))

    # AllDifferent constraints within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([nat_pos[n] for n in Nationalities]))
    s.add(Distinct([vac_pos[v] for v in Vacations]))
    s.add(Distinct([edu_pos[e] for e in Educations]))
    s.add(Distinct([occ_pos[o] for o in Occupations]))

    # Helper lambdas for readability
    pos_name = lambda n: name_pos[n]
    pos_nat = lambda n: nat_pos[n]
    pos_vac = lambda v: vac_pos[v]
    pos_edu = lambda e: edu_pos[e]
    pos_occ = lambda o: occ_pos[o]

    # Clues implementation:

    # 1. Cruise == Lawyer
    s.add(pos_vac('cruise') == pos_occ('lawyer'))

    # 2. Beach is directly left of Arnold
    s.add(pos_vac('beach') + 1 == pos_name('Arnold'))

    # 3. Doctorate is somewhere to the left of Bob
    s.add(pos_edu('doctorate') < pos_name('Bob'))

    # 4. Associate == Cruise
    s.add(pos_edu('associate') == pos_vac('cruise'))

    # 5. Peter is not in the first house
    s.add(pos_name('Peter') != 1)

    # 6. Artist == Peter
    s.add(pos_occ('artist') == pos_name('Peter'))

    # 7. Camping == Master
    s.add(pos_vac('camping') == pos_edu('master'))

    # 8. Dane is somewhere to the right of the Doctor (occupation)
    s.add(pos_nat('dane') > pos_occ('doctor'))

    # 9. Associate is directly left of Engineer
    s.add(pos_edu('associate') + 1 == pos_occ('engineer'))

    # 10. Camping == British
    s.add(pos_vac('camping') == pos_nat('brit'))

    # 11. Norwegian and Bachelor are next to each other
    s.add(Or(pos_nat('norwegian') == pos_edu('bachelor') + 1,
             pos_nat('norwegian') == pos_edu('bachelor') - 1))

    # 12. Artist == Swedish
    s.add(pos_occ('artist') == pos_nat('swede'))

    # 13. Bob is not in the fourth house
    s.add(pos_name('Bob') != 4)

    # 14. Camping == Eric
    s.add(pos_vac('camping') == pos_name('Eric'))

    # 15. Alice == German
    s.add(pos_name('Alice') == pos_nat('german'))

    # 16. Beach is somewhere to the left of City
    s.add(pos_vac('beach') < pos_vac('city'))

    # 17. Mountain is in the fifth house
    s.add(pos_vac('mountain') == 5)

    # 18. Cruise is somewhere to the right of Beach
    s.add(pos_vac('cruise') > pos_vac('beach'))

    # 19. Bachelor is in the third house
    s.add(pos_edu('bachelor') == 3)

    # Solve
    if s.check() != sat:
        output = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    m = s.model()

    # Build inverse maps: house -> attribute
    def invert(group, items):
        inv = {}
        for item in items:
            inv[m.evaluate(group[item]).as_long()] = item
        return inv

    inv_name = invert(name_pos, Names)
    inv_nat = invert(nat_pos, Nationalities)
    inv_vac = invert(vac_pos, Vacations)
    inv_edu = invert(edu_pos, Educations)
    inv_occ = invert(occ_pos, Occupations)

    rows = []
    for h in sorted(houses):
        rows.append([
            str(h),
            inv_name[h],
            inv_nat[h],
            inv_vac[h],
            inv_edu[h],
            inv_occ[h]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()