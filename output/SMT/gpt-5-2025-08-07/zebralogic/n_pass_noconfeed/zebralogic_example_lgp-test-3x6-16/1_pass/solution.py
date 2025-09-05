import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def main():
    n_houses = 3
    houses = range(1, n_houses + 1)

    # Attribute values
    Names = ["Eric", "Peter", "Arnold"]
    Drinks = ["tea", "water", "milk"]
    Nationalities = ["dane", "brit", "swede"]
    Educations = ["high school", "associate", "bachelor"]
    HouseStyles = ["victorian", "colonial", "ranch"]
    Smoothies = ["cherry", "watermelon", "desert"]

    # Create position variables for each attribute value: value -> house index (1..3)
    name_pos = {v: Int(f"name_{v}") for v in Names}
    drink_pos = {v: Int(f"drink_{v}") for v in Drinks}
    nat_pos = {v: Int(f"nat_{v}") for v in Nationalities}
    edu_pos = {v: Int(f"edu_{v}") for v in Educations}
    style_pos = {v: Int(f"style_{v}") for v in HouseStyles}
    smoothie_pos = {v: Int(f"smoothie_{v}") for v in Smoothies}

    s = Solver()

    # Domain constraints: each variable is in 1..3
    for mp in [name_pos, drink_pos, nat_pos, edu_pos, style_pos, smoothie_pos]:
        for v in mp.values():
            s.add(And(v >= 1, v <= n_houses))

    # All-different constraints within each category
    s.add(Distinct([name_pos[v] for v in Names]))
    s.add(Distinct([drink_pos[v] for v in Drinks]))
    s.add(Distinct([nat_pos[v] for v in Nationalities]))
    s.add(Distinct([edu_pos[v] for v in Educations]))
    s.add(Distinct([style_pos[v] for v in HouseStyles]))
    s.add(Distinct([smoothie_pos[v] for v in Smoothies]))

    # Clues:
    # 1. There is one house between Eric and the tea drinker.
    s.add(Abs(name_pos["Eric"] - drink_pos["tea"]) == 2)

    # 2. The person who likes milk is the person in a ranch-style home.
    s.add(drink_pos["milk"] == style_pos["ranch"])

    # 3. The person with a bachelor's degree is in the second house.
    s.add(edu_pos["bachelor"] == 2)

    # 4. The person with a high school diploma is the Dane.
    s.add(edu_pos["high school"] == nat_pos["dane"])

    # 5. The Desert smoothie lover is the Swedish person.
    s.add(smoothie_pos["desert"] == nat_pos["swede"])

    # 6. The person residing in a Victorian house is not in the first house.
    s.add(style_pos["victorian"] != 1)

    # 7. The person who likes Cherry smoothies is the person living in a colonial-style house.
    s.add(smoothie_pos["cherry"] == style_pos["colonial"])

    # 8. Arnold is somewhere to the right of the person residing in a Victorian house.
    s.add(name_pos["Arnold"] > style_pos["victorian"])

    # 9. The person in a ranch-style home is the person with a high school diploma.
    s.add(style_pos["ranch"] == edu_pos["high school"])

    assert s.check().r == 1, "No solution found"

    m = s.model()

    def value_for_house(pos_map, house):
        for k, v in pos_map.items():
            if m.evaluate(v).as_long() == house:
                return k
        return None

    header = ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"]
    rows = []
    for h in houses:
        row = [
            str(h),
            value_for_house(name_pos, h),
            value_for_house(drink_pos, h),
            value_for_house(nat_pos, h),
            value_for_house(edu_pos, h),
            value_for_house(style_pos, h),
            value_for_house(smoothie_pos, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()