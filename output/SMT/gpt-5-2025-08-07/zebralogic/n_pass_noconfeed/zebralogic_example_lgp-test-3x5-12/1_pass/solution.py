import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def main():
    houses = [1, 2, 3]

    # Define categories and options
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    # Create Z3 variables: each value maps to a house position 1..3
    def create_vars(options, prefix):
        return {opt: Int(f"{prefix}_{opt.replace(' ', '_')}") for opt in options}

    name_pos = create_vars(names, "name")
    cigar_pos = create_vars(cigars, "cigar")
    hobby_pos = create_vars(hobbies, "hobby")
    edu_pos = create_vars(educations, "edu")
    drink_pos = create_vars(drinks, "drink")

    s = Solver()

    # Domain constraints: each position between 1 and 3
    for pos_dict in [name_pos, cigar_pos, hobby_pos, edu_pos, drink_pos]:
        for var in pos_dict.values():
            s.add(And(var >= 1, var <= 3))
        # All different within each category
        s.add(Distinct(*pos_dict.values()))

    # Clues:
    # 1. The person partial to Pall Mall is Peter.
    s.add(cigar_pos["pall mall"] == name_pos["Peter"])

    # 2. The person who likes milk is directly left of the person with a high school diploma.
    s.add(drink_pos["milk"] + 1 == edu_pos["high school"])

    # 3. Eric is the tea drinker.
    s.add(name_pos["Eric"] == drink_pos["tea"])

    # 4. Arnold and the Prince smoker are next to each other.
    s.add(Abs(name_pos["Arnold"] - cigar_pos["prince"]) == 1)

    # 5. The person who enjoys gardening is somewhere to the left of the Prince smoker.
    s.add(hobby_pos["gardening"] < cigar_pos["prince"])

    # 6. The person who likes milk is the person with an associate's degree.
    s.add(drink_pos["milk"] == edu_pos["associate"])

    # 7. The person with a bachelor's degree is directly left of the photography enthusiast.
    s.add(edu_pos["bachelor"] + 1 == hobby_pos["photography"])

    # Solve
    if s.check() != 1:  # 1 corresponds to sat
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Invert position mappings to "house -> value"
    def invert(pos_dict):
        inv = {}
        for val, var in pos_dict.items():
            inv[m[var].as_long()] = val
        return inv

    inv_name = invert(name_pos)
    inv_cigar = invert(cigar_pos)
    inv_hobby = invert(hobby_pos)
    inv_edu = invert(edu_pos)
    inv_drink = invert(drink_pos)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_cigar[h],
            inv_hobby[h],
            inv_edu[h],
            inv_drink[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()