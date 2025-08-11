import json
from copy import deepcopy

def solve():
    # Categories and their possible values
    categories = [
        "name",
        "hobby",
        "birthday month",
        "level of education",
        "favorite smoothie",
    ]

    values = {
        "name": ["Arnold", "Alice", "Eric", "Peter"],
        "hobby": ["cooking", "painting", "photography", "gardening"],
        "birthday month": ["april", "jan", "sept", "feb"],
        "level of education": ["master", "bachelor", "associate", "high school"],
        "favorite smoothie": ["cherry", "watermelon", "desert", "dragonfruit"],
    }

    # Initialize 4 houses (index 0..3 => house 1..4)
    houses = [{cat: None for cat in categories} for _ in range(4)]

    # Remaining values for uniqueness per category
    remaining = {cat: set(vals) for cat, vals in values.items()}

    # Apply fixed clues directly:
    # Clue 4: The person with a high school diploma is in the third house.
    houses[2]["level of education"] = "high school"
    remaining["level of education"].remove("high school")

    # Clue 9 ties high school with September -> set month for house 3
    houses[2]["birthday month"] = "sept"
    remaining["birthday month"].remove("sept")

    # Helper consistency check
    def is_consistent(hs):
        # Uniqueness for each category
        for cat in categories:
            assigned = [hs[i][cat] for i in range(4) if hs[i][cat] is not None]
            if len(assigned) != len(set(assigned)):
                return False

        # Clue 4: High school is in the third house (house index 2)
        for i in range(4):
            if i == 2:
                if hs[i]["level of education"] is not None and hs[i]["level of education"] != "high school":
                    return False
            else:
                if hs[i]["level of education"] == "high school":
                    return False

        # Clue 5: Watermelon smoothie lover is not in the third house
        if hs[2]["favorite smoothie"] == "watermelon":
            return False

        # Clue 1 and 3 combined:
        # 1: Desert smoothie lover is the person whose birthday is in January.
        # 3: The person whose birthday is in January is the person with a bachelor's degree.
        # So: desert <-> jan <-> bachelor
        for i in range(4):
            sm = hs[i]["favorite smoothie"]
            mo = hs[i]["birthday month"]
            ed = hs[i]["level of education"]

            if sm == "desert":
                if mo is not None and mo != "jan":
                    return False
                if ed is not None and ed != "bachelor":
                    return False
            if mo == "jan":
                if sm is not None and sm != "desert":
                    return False
                if ed is not None and ed != "bachelor":
                    return False
            if ed == "bachelor":
                if mo is not None and mo != "jan":
                    return False
                if sm is not None and sm != "desert":
                    return False

        # Clue 2: Eric is the person with a bachelor's degree.
        for i in range(4):
            nm = hs[i]["name"]
            ed = hs[i]["level of education"]
            if nm == "Eric":
                if ed is not None and ed != "bachelor":
                    return False
            if ed == "bachelor":
                if nm is not None and nm != "Eric":
                    return False

        # Clue 6: The person with an associate's degree is Arnold.
        for i in range(4):
            nm = hs[i]["name"]
            ed = hs[i]["level of education"]
            if nm == "Arnold":
                if ed is not None and ed != "associate":
                    return False
            if ed == "associate":
                if nm is not None and nm != "Arnold":
                    return False

        # Clue 7: The person with a master's degree paints.
        # Clue 12: The painter has birthday in February.
        # Therefore: master <-> painting <-> feb
        for i in range(4):
            ed = hs[i]["level of education"]
            hb = hs[i]["hobby"]
            mo = hs[i]["birthday month"]

            if ed == "master":
                if hb is not None and hb != "painting":
                    return False
                if mo is not None and mo != "feb":
                    return False
            if hb == "painting":
                if ed is not None and ed != "master":
                    return False
                if mo is not None and mo != "feb":
                    return False
            if mo == "feb":
                if hb is not None and hb != "painting":
                    return False
                if ed is not None and ed != "master":
                    return False

        # Clue 9: High school diploma is the person whose birthday is in September.
        for i in range(4):
            ed = hs[i]["level of education"]
            mo = hs[i]["birthday month"]
            if ed == "high school":
                if mo is not None and mo != "sept":
                    return False
            if mo == "sept":
                if ed is not None and ed != "high school":
                    return False

        # Clue 8: One house between Dragonfruit smoothie lover and the person whose birthday is in September.
        dragon_idx = None
        sept_idx = None
        for i in range(4):
            if hs[i]["favorite smoothie"] == "dragonfruit":
                dragon_idx = i
            if hs[i]["birthday month"] == "sept":
                sept_idx = i
        if dragon_idx is not None and sept_idx is not None:
            if abs(dragon_idx - sept_idx) != 2:
                return False

        # Clue 10: The person who loves cooking is Alice.
        for i in range(4):
            nm = hs[i]["name"]
            hb = hs[i]["hobby"]
            if nm == "Alice":
                if hb is not None and hb != "cooking":
                    return False
            if hb == "cooking":
                if nm is not None and nm != "Alice":
                    return False

        # Clue 11: April and Gardening are next to each other.
        april_idx = None
        garden_idx = None
        for i in range(4):
            if hs[i]["birthday month"] == "april":
                april_idx = i
            if hs[i]["hobby"] == "gardening":
                garden_idx = i
        if april_idx is not None and garden_idx is not None:
            if abs(april_idx - garden_idx) != 1:
                return False

        return True

    # Variable ordering with MRV
    def next_variable(hs, rem):
        best = None
        best_domain = None
        for i in range(4):
            for cat in categories:
                if hs[i][cat] is None:
                    # Build domain candidates from remaining
                    domain = list(rem[cat])
                    # Apply immediate static domain prunes
                    if cat == "favorite smoothie" and i == 2:
                        domain = [v for v in domain if v != "watermelon"]
                    if cat == "level of education":
                        if i == 2:
                            domain = [v for v in domain if v == "high school"]
                        else:
                            domain = [v for v in domain if v != "high school"]
                    # Test each candidate with consistency check
                    filtered = []
                    for v in domain:
                        hs[i][cat] = v
                        if is_consistent(hs):
                            filtered.append(v)
                        hs[i][cat] = None
                    domain = filtered

                    if best is None or len(domain) < len(best_domain):
                        best = (i, cat)
                        best_domain = domain
                        if len(best_domain) == 0:
                            return best, best_domain
        return best, best_domain

    def backtrack(hs, rem):
        # If all assigned
        done = True
        for i in range(4):
            for cat in categories:
                if hs[i][cat] is None:
                    done = False
                    break
            if not done:
                break
        if done:
            if is_consistent(hs):
                return hs
            return None

        (i, cat), domain = next_variable(hs, rem)
        if domain is None or len(domain) == 0:
            return None

        for v in domain:
            hs[i][cat] = v
            rem[cat].remove(v)
            if is_consistent(hs):
                result = backtrack(hs, rem)
                if result is not None:
                    return result
            rem[cat].add(v)
            hs[i][cat] = None
        return None

    solution = backtrack(deepcopy(houses), deepcopy(remaining))
    return solution

def main():
    solution = solve()
    header = ["House", "name", "hobby", "birthday month", "level of education", "favorite smoothie"]
    rows = []
    for idx, house in enumerate(solution, start=1):
        row = [
            str(idx),
            house["name"],
            house["hobby"],
            house["birthday month"],
            house["level of education"],
            house["favorite smoothie"],
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