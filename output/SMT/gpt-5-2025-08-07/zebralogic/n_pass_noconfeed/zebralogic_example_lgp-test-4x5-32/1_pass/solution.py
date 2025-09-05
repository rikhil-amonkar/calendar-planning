import json
from z3 import Solver, Int, And, Distinct, Abs, sat

def main():
    houses = [1, 2, 3, 4]

    # Create solver
    s = Solver()

    # Categories and their items
    Names = ["Arnold", "Alice", "Eric", "Peter"]
    Hobbies = ["cooking", "painting", "photography", "gardening"]
    Birthdays = ["april", "jan", "sept", "feb"]
    Education = ["master", "bachelor", "associate", "high school"]
    Smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Create position variables (house index) for each item
    name_pos = {n: Int(f"pos_name_{n}") for n in Names}
    hobby_pos = {h: Int(f"pos_hobby_{h}") for h in Hobbies}
    bday_pos = {b: Int(f"pos_bday_{b}") for b in Birthdays}
    edu_pos = {e: Int(f"pos_edu_{e.replace(' ', '_')}") for e in Education}
    smoothie_pos = {smo: Int(f"pos_smoothie_{smo}") for smo in Smoothies}

    # All variables are in range 1..4
    for D in (name_pos, hobby_pos, bday_pos, edu_pos, smoothie_pos):
        for v in D.values():
            s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct(list(name_pos.values())))
    s.add(Distinct(list(hobby_pos.values())))
    s.add(Distinct(list(bday_pos.values())))
    s.add(Distinct(list(edu_pos.values())))
    s.add(Distinct(list(smoothie_pos.values())))

    # Clues constraints:

    # 1. The Desert smoothie lover is the person whose birthday is in January.
    s.add(smoothie_pos["desert"] == bday_pos["jan"])

    # 2. Eric is the person with a bachelor's degree.
    s.add(name_pos["Eric"] == edu_pos["bachelor"])

    # 3. The person whose birthday is in January is the person with a bachelor's degree.
    s.add(bday_pos["jan"] == edu_pos["bachelor"])

    # 4. The person with a high school diploma is in the third house.
    s.add(edu_pos["high school"] == 3)

    # 5. The Watermelon smoothie lover is not in the third house.
    s.add(smoothie_pos["watermelon"] != 3)

    # 6. The person with an associate's degree is Arnold.
    s.add(edu_pos["associate"] == name_pos["Arnold"])

    # 7. The person with a master's degree is the person who paints as a hobby.
    s.add(edu_pos["master"] == hobby_pos["painting"])

    # 8. There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    s.add(Abs(smoothie_pos["dragonfruit"] - bday_pos["sept"]) == 2)

    # 9. The person with a high school diploma is the person whose birthday is in September.
    s.add(edu_pos["high school"] == bday_pos["sept"])

    # 10. The person who loves cooking is Alice.
    s.add(hobby_pos["cooking"] == name_pos["Alice"])

    # 11. The person whose birthday is in April and the person who enjoys gardening are next to each other.
    s.add(Abs(bday_pos["april"] - hobby_pos["gardening"]) == 1)

    # 12. The person who paints as a hobby is the person whose birthday is in February.
    s.add(hobby_pos["painting"] == bday_pos["feb"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Helper: invert category positions to get value at each house
    def value_at_house(pos_dict, house):
        for k, v in pos_dict.items():
            if m.eval(v).as_long() == house:
                return k
        return None

    rows = []
    for h in houses:
        name = value_at_house(name_pos, h)
        hobby = value_at_house(hobby_pos, h)
        bday = value_at_house(bday_pos, h)
        edu = value_at_house(edu_pos, h)
        smo = value_at_house(smoothie_pos, h)
        rows.append([str(h), name, hobby, bday, edu, smo])

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()