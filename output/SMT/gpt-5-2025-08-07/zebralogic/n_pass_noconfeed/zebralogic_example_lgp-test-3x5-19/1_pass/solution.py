import json
from z3 import Solver, Int, And, Distinct

def var_name(category, item):
    return f"{category}_{item}".replace(" ", "_")

def main():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Arnold", "Peter", "Eric"],
        "Occupation": ["doctor", "teacher", "engineer"],
        "Education": ["associate", "high school", "bachelor"],
        "Smoothie": ["desert", "cherry", "watermelon"],
        "Hobby": ["gardening", "cooking", "photography"],
    }

    # Create Z3 variables for each item in each category representing house positions
    vars_by_cat = {}
    for cat, items in categories.items():
        vars_by_cat[cat] = {item: Int(var_name(cat, item)) for item in items}

    s = Solver()

    # Domain constraints and uniqueness within each category
    for cat, items in categories.items():
        cat_vars = list(vars_by_cat[cat].values())
        for v in cat_vars:
            s.add(And(v >= houses[0], v <= houses[-1]))
        s.add(Distinct(cat_vars))

    # Helper accessors
    Name = vars_by_cat["Name"]
    Occup = vars_by_cat["Occupation"]
    Edu = vars_by_cat["Education"]
    Sm = vars_by_cat["Smoothie"]
    Hobby = vars_by_cat["Hobby"]

    # Clues:
    # 1. The Desert smoothie lover is the person who is a doctor.
    s.add(Sm["desert"] == Occup["doctor"])

    # 2. Arnold is not in the third house.
    s.add(Name["Arnold"] != 3)

    # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
    s.add(Sm["cherry"] > Name["Peter"])

    # 4. The person who loves cooking is in the second house.
    s.add(Hobby["cooking"] == 2)

    # 5. The person who loves cooking is Peter.
    s.add(Hobby["cooking"] == Name["Peter"])

    # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    s.add(Edu["associate"] > Hobby["gardening"])

    # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    s.add(Edu["bachelor"] > Sm["desert"])

    # 8. The person who loves cooking is the person who is a doctor.
    s.add(Hobby["cooking"] == Occup["doctor"])

    # 9. The photography enthusiast is the person who is a teacher.
    s.add(Hobby["photography"] == Occup["teacher"])

    if s.check() != 1:  # sat
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    def item_at_house(cat, house):
        for item, var in vars_by_cat[cat].items():
            if m[var].as_long() == house:
                return item
        return None

    header = ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            item_at_house("Name", h),
            item_at_house("Occupation", h),
            item_at_house("Education", h),
            item_at_house("Smoothie", h),
            item_at_house("Hobby", h),
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