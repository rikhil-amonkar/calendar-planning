import json
from z3 import Solver, Int, Distinct, And, Or, sat

def main():
    n = 4
    houses = range(1, n + 1)

    # Categories and values
    Names = ["Peter", "Alice", "Eric", "Arnold"]
    Mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    Smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    Heights = ["tall", "average", "short", "very short"]
    Educations = ["high school", "associate", "master", "bachelor"]

    # Create Z3 variables for each attribute value indicating the house number
    def make_vars(prefix, items):
        return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

    name = make_vars("Name", Names)
    mother = make_vars("Mother", Mothers)
    smoothie = make_vars("Smoothie", Smoothies)
    height = make_vars("Height", Heights)
    education = make_vars("Education", Educations)

    s = Solver()

    # Domain constraints: each variable is in 1..4
    for group in [name, mother, smoothie, height, education]:
        for v in group.values():
            s.add(And(v >= 1, v <= n))

    # All-different constraints within each category
    s.add(Distinct(*name.values()))
    s.add(Distinct(*mother.values()))
    s.add(Distinct(*smoothie.values()))
    s.add(Distinct(*height.values()))
    s.add(Distinct(*education.values()))

    # Helper relations
    def next_to(a, b):
        return Or(a == b + 1, a == b - 1)

    # Clues:
    # 1. The person whose mother's name is Janelle is in the third house.
    s.add(mother["Janelle"] == 3)

    # 2. The Desert smoothie lover is the person with a master's degree.
    s.add(smoothie["desert"] == education["master"])

    # 3. The Desert smoothie lover is not in the first house.
    s.add(smoothie["desert"] != 1)

    # 4. The person who is very short is somewhere to the left of the person with a high school diploma.
    s.add(height["very short"] < education["high school"])

    # 5. Eric and the person who likes Cherry smoothies are next to each other.
    s.add(next_to(name["Eric"], smoothie["cherry"]))

    # 6. The person with a high school diploma is not in the third house.
    s.add(education["high school"] != 3)

    # 7. The person whose mother's name is Kailyn is the person with an associate's degree.
    s.add(mother["Kailyn"] == education["associate"])

    # 8. The person who likes Cherry smoothies is The person whose mother's name is Aniya.
    s.add(smoothie["cherry"] == mother["Aniya"])

    # 9. The person who is tall is The person whose mother's name is Janelle.
    s.add(height["tall"] == mother["Janelle"])

    # 10. Arnold is somewhere to the right of the person who has an average height.
    s.add(name["Arnold"] > height["average"])

    # 11. The Dragonfruit smoothie lover is directly left of the person who is short.
    s.add(smoothie["dragonfruit"] + 1 == height["short"])

    # 12. The person who is tall is Alice.
    s.add(height["tall"] == name["Alice"])

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    # Build house -> attribute mapping
    def value_at_house(group, house_num):
        for k, v in group.items():
            if m[v].as_long() == house_num:
                return k
        return None

    header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            value_at_house(name, h),
            value_at_house(mother, h),
            value_at_house(smoothie, h),
            value_at_house(height, h),
            value_at_house(education, h),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()