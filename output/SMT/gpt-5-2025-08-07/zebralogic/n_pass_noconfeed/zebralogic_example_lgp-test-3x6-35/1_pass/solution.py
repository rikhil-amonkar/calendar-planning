import json
from z3 import Solver, Int, And, Distinct, sat

def main():
    houses = [1, 2, 3]

    # Domain values
    Names = ["Eric", "Arnold", "Peter"]
    Vacations = ["mountain", "city", "beach"]
    Heights = ["very short", "average", "short"]
    Flowers = ["carnations", "daffodils", "lilies"]
    HairColors = ["brown", "black", "blonde"]
    Educations = ["associate", "bachelor", "high school"]

    # Create Z3 Int variables for each value representing the house number (1..3)
    def mkvars(vals, prefix_map=None):
        m = {}
        for v in vals:
            var_name = v
            if prefix_map and v in prefix_map:
                var_name = prefix_map[v]
            else:
                var_name = v.replace(" ", "_")
            m[v] = Int(var_name)
        return m

    names = mkvars(Names)
    vacations = mkvars(Vacations)
    heights = mkvars(Heights, {"very short": "very_short"})
    flowers = mkvars(Flowers)
    hair = mkvars(HairColors)
    education = mkvars(Educations, {"high school": "high_school"})

    s = Solver()

    # Domain constraints: each variable is in 1..3
    def domain_constraints(varmap):
        return [And(varmap[v] >= 1, varmap[v] <= 3) for v in varmap]

    s.add(domain_constraints(names))
    s.add(domain_constraints(vacations))
    s.add(domain_constraints(heights))
    s.add(domain_constraints(flowers))
    s.add(domain_constraints(hair))
    s.add(domain_constraints(education))

    # AllDifferent within each attribute category
    s.add(Distinct([names[v] for v in Names]))
    s.add(Distinct([vacations[v] for v in Vacations]))
    s.add(Distinct([heights[v] for v in Heights]))
    s.add(Distinct([flowers[v] for v in Flowers]))
    s.add(Distinct([hair[v] for v in HairColors]))
    s.add(Distinct([education[v] for v in Educations]))

    # Clues:
    # 1. Peter is the person who has an average height.
    s.add(names["Peter"] == heights["average"])

    # 2. The person who loves a bouquet of daffodils is Arnold.
    s.add(flowers["daffodils"] == names["Arnold"])

    # 3. The person who is very short is not in the second house.
    s.add(heights["very short"] != 2)

    # 4. The person who loves beach vacations is in the first house.
    s.add(vacations["beach"] == 1)

    # 5. The person with a high school diploma is in the third house.
    s.add(education["high school"] == 3)

    # 6. The person who is short is somewhere to the right of the person who is very short.
    s.add(heights["short"] > heights["very short"])

    # 7. The person who loves the boquet of lilies is Eric.
    s.add(flowers["lilies"] == names["Eric"])

    # 8. The person who loves the boquet of lilies is the person with a bachelor's degree.
    s.add(flowers["lilies"] == education["bachelor"])

    # 9. The person who prefers city breaks is somewhere to the right of Peter.
    s.add(vacations["city"] > names["Peter"])

    # 10. The person who has blonde hair is in the third house.
    s.add(hair["blonde"] == 3)

    # 11. The person who loves beach vacations is the person who has brown hair.
    s.add(vacations["beach"] == hair["brown"])

    if s.check() != sat:
        print(json.dumps({"solution": {"header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"], "rows": []}}))
        return

    model = s.model()

    # Helper to get the value assigned to a given house for a category
    def value_at_house(varmap, values, house_num):
        for val in values:
            if model[varmap[val]].as_long() == house_num:
                return val
        return None

    rows = []
    for h in houses:
        row = [
            str(h),
            value_at_house(names, Names, h),
            value_at_house(vacations, Vacations, h),
            value_at_house(heights, Heights, h),
            value_at_house(flowers, Flowers, h),
            value_at_house(hair, HairColors, h),
            value_at_house(education, Educations, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()