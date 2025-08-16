from z3 import *

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    # Categories
    Names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    Nats = ["norwegian", "brit", "swede", "dane", "german"]
    Vacs = ["cruise", "mountain", "camping", "beach", "city"]
    Edus = ["bachelor", "master", "associate", "doctorate", "high school"]
    Occs = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Create variables: position (house number) of each attribute value
    n = {name: Int(f"name_{name}") for name in Names}
    nat = {nat_: Int(f"nat_{nat_}") for nat_ in Nats}
    v = {vac: Int(f"vac_{vac}") for vac in Vacs}
    e = {edu: Int(f"edu_{edu.replace(' ', '_')}") for edu in Edus}
    o = {occ: Int(f"occ_{occ}") for occ in Occs}

    s = Solver()

    # Domains
    for d in [n, nat, v, e, o]:
        for var in d.values():
            s.add(And(var >= 1, var <= 5))

    # AllDifferent within each category
    s.add(Distinct([n[x] for x in Names]))
    s.add(Distinct([nat[x] for x in Nats]))
    s.add(Distinct([v[x] for x in Vacs]))
    s.add(Distinct([e[x] for x in Edus]))
    s.add(Distinct([o[x] for x in Occs]))

    # Clues
    # 1. cruises == lawyer
    s.add(v["cruise"] == o["lawyer"])

    # 2. beach directly left of Arnold
    s.add(v["beach"] + 1 == n["Arnold"])

    # 3. doctorate left of Bob
    s.add(e["doctorate"] < n["Bob"])

    # 4. associate == cruise
    s.add(e["associate"] == v["cruise"])

    # 5. Peter not in the first house
    s.add(n["Peter"] != 1)

    # 6. artist is Peter
    s.add(o["artist"] == n["Peter"])

    # 7. camping == master
    s.add(v["camping"] == e["master"])

    # 8. Dane is somewhere to the right of the doctor (occupation)
    s.add(nat["dane"] > o["doctor"])

    # 9. associate directly left of engineer
    s.add(e["associate"] + 1 == o["engineer"])

    # 10. camping is the British person
    s.add(v["camping"] == nat["brit"])

    # 11. Norwegian and bachelor's are next to each other
    s.add(Abs(nat["norwegian"] - e["bachelor"]) == 1)

    # 12. artist is the Swedish person
    s.add(o["artist"] == nat["swede"])

    # 13. Bob not in the fourth house
    s.add(n["Bob"] != 4)

    # 14. camping is Eric
    s.add(v["camping"] == n["Eric"])

    # 15. Alice is the German
    s.add(n["Alice"] == nat["german"])

    # 16. beach left of city
    s.add(v["beach"] < v["city"])

    # 17. mountain in the fifth house
    s.add(v["mountain"] == 5)

    # 18. cruise right of beach
    s.add(v["cruise"] > v["beach"])

    # 19. bachelor's in the third house
    s.add(e["bachelor"] == 3)

    assert s.check() == sat
    m = s.model()

    # Build inverse maps: for each house, get each attribute
    by_house = {i: {} for i in houses}

    for name in Names:
        by_house[m[n[name]].as_long()]["Name"] = name
    for nat_ in Nats:
        by_house[m[nat[nat_]].as_long()]["Nationality"] = nat_
    for vac in Vacs:
        by_house[m[v[vac]].as_long()]["Vacation"] = vac
    for edu in Edus:
        by_house[m[e[edu]].as_long()]["Education"] = edu
    for occ in Occs:
        by_house[m[o[occ]].as_long()]["Occupation"] = occ

    # Construct the JSON-like result
    result = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": []
        }
    }

    for i in houses:
        row = [
            str(i),
            by_house[i]["Name"],
            by_house[i]["Nationality"],
            by_house[i]["Vacation"],
            by_house[i]["Education"],
            by_house[i]["Occupation"],
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    import json
    print(json.dumps(solve_puzzle(), ensure_ascii=False, indent=2))