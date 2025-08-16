import json
from z3 import Solver, Int, Distinct, And, Or, If, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    Hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
    Sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    Styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    Children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    Heights = ["average", "very tall", "very short", "short", "tall"]

    # Helper to create Z3 variables mapping each value in a category to a house number (1..5)
    def make_vars(prefix, values):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    name_pos = make_vars("name", Names)
    hobby_pos = make_vars("hobby", Hobbies)
    sport_pos = make_vars("sport", Sports)
    style_pos = make_vars("style", Styles)
    child_pos = make_vars("child", Children)
    height_pos = make_vars("height", Heights)

    s = Solver()

    # Domain constraints: every variable is in 1..5
    for cat in [name_pos, hobby_pos, sport_pos, style_pos, child_pos, height_pos]:
        for v in cat.values():
            s.add(And(v >= 1, v <= 5))
        # All distinct within a category
        s.add(Distinct(*cat.values()))

    # Clues translated to constraints

    # 1. average height <-> child Meredith
    s.add(height_pos["average"] == child_pos["Meredith"])

    # 2. tall is in second house
    s.add(height_pos["tall"] == 2)

    # 3. Peter is directly left of the Victorian house
    s.add(name_pos["Peter"] + 1 == style_pos["victorian"])

    # 4. Alice is tall
    s.add(name_pos["Alice"] == height_pos["tall"])

    # 5. baseball <-> very tall
    s.add(sport_pos["baseball"] == height_pos["very tall"])

    # 6. Meredith and Timothy are next to each other
    s.add(Abs(child_pos["Meredith"] - child_pos["Timothy"]) == 1)

    # 7. Bob paints
    s.add(name_pos["Bob"] == hobby_pos["painting"])

    # 8. gardening is in the second house
    s.add(hobby_pos["gardening"] == 2)

    # 9. very short is somewhere to the right of Eric
    s.add(height_pos["very short"] > name_pos["Eric"])

    # 10. tennis <-> Samantha
    s.add(sport_pos["tennis"] == child_pos["Samantha"])

    # 11. soccer is not in the first house
    s.add(sport_pos["soccer"] != 1)

    # 12. Samantha <-> modern
    s.add(child_pos["Samantha"] == style_pos["modern"])

    # 13. craftsman <-> average
    s.add(style_pos["craftsman"] == height_pos["average"])

    # 14. Fred <-> victorian
    s.add(child_pos["Fred"] == style_pos["victorian"])

    # 15. short <-> basketball
    s.add(height_pos["short"] == sport_pos["basketball"])

    # 16. Peter <-> very tall
    s.add(name_pos["Peter"] == height_pos["very tall"])

    # 17. ranch is somewhere to the left of cooking
    s.add(style_pos["ranch"] < hobby_pos["cooking"])

    # 18. knitting and gardening are next to each other
    s.add(Abs(hobby_pos["knitting"] - hobby_pos["gardening"]) == 1)

    # 19. modern <-> cooking
    s.add(style_pos["modern"] == hobby_pos["cooking"])

    # 20. victorian is in the fifth house
    s.add(style_pos["victorian"] == 5)

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    # Build reverse maps: for each house, find the assigned value for each category
    def invert(cat_values, cat_pos):
        inv = {}
        for val in cat_values:
            inv[int(m[cat_pos[val]].as_long())] = val
        return inv

    name_at = invert(Names, name_pos)
    hobby_at = invert(Hobbies, hobby_pos)
    sport_at = invert(Sports, sport_pos)
    style_at = invert(Styles, style_pos)
    child_at = invert(Children, child_pos)
    height_at = invert(Heights, height_pos)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_at[h],
            hobby_at[h],
            sport_at[h],
            style_at[h],
            child_at[h],
            height_at[h],
        ])

    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": rows
        }
    }
    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))