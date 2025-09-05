import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    Names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    Mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    Heights = ["average", "very short", "short", "very tall", "tall"]

    # Helper predicates
    def left_of(a, b):
        return a < b

    def direct_left_of(a, b):
        return a + 1 == b

    solution = None

    # Search over permutations with pruning
    for name_perm in itertools.permutations(houses):
        pos_name = {Names[i]: name_perm[i] for i in range(5)}

        # Early pruning using name-only constraints
        # 4. Peter is not in the second house.
        if pos_name["Peter"] == 2:
            continue
        # 8. Eric is not in the fifth house.
        if pos_name["Eric"] == 5:
            continue
        # 5. The person who is short is directly left of Arnold. => Arnold not in 1
        if pos_name["Arnold"] == 1:
            continue
        # 7. Bob is directly left of the person who has an average height. => Bob not in 5
        if pos_name["Bob"] == 5:
            continue

        for mother_perm in itertools.permutations(houses):
            pos_mother = {Mothers[i]: mother_perm[i] for i in range(5)}

            # 1. Alice is The person whose mother's name is Aniya.
            if pos_name["Alice"] != pos_mother["Aniya"]:
                continue
            # 3. The person whose mother's name is Janelle is Bob.
            if pos_mother["Janelle"] != pos_name["Bob"]:
                continue
            # 10. Eric is The person whose mother's name is Kailyn.
            if pos_mother["Kailyn"] != pos_name["Eric"]:
                continue
            # 9 involves height; skip for now
            # 2 involves height; skip for now

            for height_perm in itertools.permutations(houses):
                pos_height = {Heights[i]: height_perm[i] for i in range(5)}

                # 11. The person who is very short is in the fifth house.
                if pos_height["very short"] != 5:
                    continue
                # 6. The person who is very tall is Arnold.
                if pos_height["very tall"] != pos_name["Arnold"]:
                    continue
                # 5. The person who is short is directly left of Arnold.
                if not direct_left_of(pos_height["short"], pos_name["Arnold"]):
                    continue
                # 7. Bob is directly left of the person who has an average height.
                if not direct_left_of(pos_name["Bob"], pos_height["average"]):
                    continue
                # 2. The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
                if not left_of(pos_height["average"], pos_mother["Penny"]):
                    continue
                # 9. The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
                if not left_of(pos_mother["Holly"], pos_height["very tall"]):
                    continue

                # All constraints satisfied
                house_to_name = {pos_name[n]: n for n in Names}
                house_to_mother = {pos_mother[m]: m for m in Mothers}
                house_to_height = {pos_height[h]: h for h in Heights}

                rows = []
                for h in houses:
                    rows.append([str(h), house_to_name[h], house_to_mother[h], house_to_height[h]])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Height"],
                        "rows": rows
                    }
                }
                return solution

    raise RuntimeError("No solution found")

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))