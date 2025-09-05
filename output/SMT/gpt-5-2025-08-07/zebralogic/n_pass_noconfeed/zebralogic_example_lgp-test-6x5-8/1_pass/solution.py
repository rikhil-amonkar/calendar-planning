import json
from z3 import *

def main():
    # Houses are positions 1..6 (left to right)
    houses = range(1, 7)

    # Categories and values
    Names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    Animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    Occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    Sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    Heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

    # Helper to create position variables for each attribute (maps attribute -> house index)
    def make_pos_vars(prefix, items):
        return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

    pos_name = make_pos_vars("name", Names)
    pos_animal = make_pos_vars("animal", Animals)
    pos_job = make_pos_vars("job", Occupations)
    pos_sport = make_pos_vars("sport", Sports)
    pos_height = make_pos_vars("height", Heights)

    s = Solver()

    # Domain constraints: each position is between 1 and 6
    def add_domain(vars_dict):
        for v in vars_dict.values():
            s.add(And(v >= 1, v <= 6))

    add_domain(pos_name)
    add_domain(pos_animal)
    add_domain(pos_job)
    add_domain(pos_sport)
    add_domain(pos_height)

    # AllDifferent constraints within each category
    s.add(Distinct(list(pos_name.values())))
    s.add(Distinct(list(pos_animal.values())))
    s.add(Distinct(list(pos_job.values())))
    s.add(Distinct(list(pos_sport.values())))
    s.add(Distinct(list(pos_height.values())))

    # Clues:
    # 1. The person who is an engineer is the dog owner.
    s.add(pos_job["engineer"] == pos_animal["dog"])

    # 2. The person who has an average height is somewhere to the left of the person who is short.
    s.add(pos_height["average"] < pos_height["short"])

    # 3. The person who has an average height is directly left of the rabbit owner.
    s.add(pos_height["average"] + 1 == pos_animal["rabbit"])

    # 4. The person who is tall is somewhere to the left of the person who is very short.
    s.add(pos_height["tall"] < pos_height["very short"])

    # 5. Arnold is the cat lover.
    s.add(pos_name["Arnold"] == pos_animal["cat"])

    # 6. The person who keeps horses is the person who is a teacher.
    s.add(pos_animal["horse"] == pos_job["teacher"])

    # 7. Carol is the person who loves soccer.
    s.add(pos_name["Carol"] == pos_sport["soccer"])

    # 8. The person who is tall is the person who loves volleyball.
    s.add(pos_height["tall"] == pos_sport["volleyball"])

    # 9. The person who is a lawyer is in the fifth house.
    s.add(pos_job["lawyer"] == 5)

    # 10. The person who loves tennis is the person who is a teacher.
    s.add(pos_sport["tennis"] == pos_job["teacher"])

    # 11. The person who has an average height is the person who loves swimming.
    s.add(pos_height["average"] == pos_sport["swimming"])

    # 12. The person who loves baseball is directly left of the person who is an engineer.
    s.add(pos_sport["baseball"] + 1 == pos_job["engineer"])

    # 13. Peter is the person who is a nurse.
    s.add(pos_name["Peter"] == pos_job["nurse"])

    # 14. Bob is somewhere to the right of the person who is an artist.
    s.add(pos_name["Bob"] > pos_job["artist"])

    # 15. The person who is a teacher is directly left of the person who loves soccer.
    s.add(pos_job["teacher"] + 1 == pos_sport["soccer"])

    # 16. The rabbit owner is Alice.
    s.add(pos_animal["rabbit"] == pos_name["Alice"])

    # 17. The fish enthusiast is Carol.
    s.add(pos_animal["fish"] == pos_name["Carol"])

    # 18. The person who loves baseball is in the first house.
    s.add(pos_sport["baseball"] == 1)

    # 19. The cat lover is somewhere to the right of the person who is very short.
    s.add(pos_animal["cat"] > pos_height["very short"])

    # 20. The person who is super tall is in the fifth house.
    s.add(pos_height["super tall"] == 5)

    # Solve
    if s.check() != sat:
        # In case of unsat (unexpected), output an empty structure to conform to JSON
        result = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Helper to invert mapping: find which attribute is at a given house
    def value_at_house(pos_dict, house):
        for k, v in pos_dict.items():
            if m.evaluate(v).as_long() == house:
                return k
        return None

    header = ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"]
    rows = []
    for h in houses:
        row = [
            str(h),
            value_at_house(pos_name, h),
            value_at_house(pos_animal, h),
            value_at_house(pos_job, h),
            value_at_house(pos_sport, h),
            value_at_house(pos_height, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()