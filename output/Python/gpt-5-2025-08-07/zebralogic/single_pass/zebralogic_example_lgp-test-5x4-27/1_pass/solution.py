import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5]

    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Try all possible assignments using backtracking with pruning via constraints
    for name_at in permutations(names):
        # C13: Eric is in the third house.
        if name_at[2] != "Eric":
            continue

        pos = {n: name_at.index(n) for n in names}
        pos_peter = pos["Peter"]
        pos_arnold = pos["Arnold"]
        pos_eric = pos["Eric"]

        # C9: Arnold is directly left of Peter.
        if not (pos_arnold + 1 == pos_peter):
            continue

        # C5: Peter is somewhere to the right of the root beer lover (Eric).
        if not (pos_peter > pos_eric):
            continue

        for bday_at in permutations(birthdays):
            # C8: The person whose birthday is in February is in the second house.
            if bday_at[1] != "feb":
                continue

            # C6: There is one house between the person whose birthday is in January and Peter.
            if abs(bday_at.index("jan") - pos_peter) != 2:
                continue

            # C3: The person whose birthday is in April is Bob.
            if bday_at[pos["Bob"]] != "april":
                continue

            pos_bday = {b: bday_at.index(b) for b in birthdays}

            for cigar_at in permutations(cigars):
                # C2: The person partial to Pall Mall is in the third house.
                if cigar_at[2] != "pall mall":
                    continue

                # C7 and C8: blends smoker is feb and feb is in the second house -> blends in second house
                if cigar_at[1] != "blends":
                    continue

                # C4: The Dunhill smoker is the person whose birthday is in March.
                if cigar_at.index("dunhill") != pos_bday["mar"]:
                    continue

                pos_cigar = {c: cigar_at.index(c) for c in cigars}

                for drink_at in permutations(drinks):
                    # C1 + C13: The root beer lover is Eric, and Eric is in house 3
                    if drink_at[pos_eric] != "root beer":
                        continue

                    # C10: The person who likes milk is not in the fifth house.
                    if drink_at[4] == "milk":
                        continue

                    # C12: There is one house between the tea drinker and the coffee drinker.
                    if abs(drink_at.index("tea") - drink_at.index("coffee")) != 2:
                        continue

                    # C11: The person who smokes Blue Master is the coffee drinker.
                    if pos_cigar["blue master"] != drink_at.index("coffee"):
                        continue

                    # All constraints satisfied; construct solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        row = [
                            str(houses[i]),
                            name_at[i],
                            bday_at[i],
                            cigar_at[i],
                            drink_at[i],
                        ]
                        result["solution"]["rows"].append(row)

                    return result

    return {"solution": {"header": ["House", "Name", "Birthday", "Cigar", "Drink"], "rows": []}}

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, ensure_ascii=False, indent=2))