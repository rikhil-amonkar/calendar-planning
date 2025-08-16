import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Generate all possible permutations for names, children, and smoothies
    for name_perm in permutations(names):
        # Constraint 9: Arnold is not in the second house
        if name_perm[1] == "Arnold":
            continue
        # Constraint 11: Arnold is directly left of Carol
        try:
            arnold_pos = name_perm.index("Arnold")
            if name_perm[arnold_pos + 1] != "Carol":
                continue
        except (ValueError, IndexError):
            continue

        for child_perm in permutations(children):
            # Constraint 6: Alice is the person's child is named Alice
            alice_name_pos = name_perm.index("Alice")
            if child_perm[alice_name_pos] != "Alice":
                continue
            # Constraint 10: Bob is the mother of Timothy
            try:
                bob_pos = name_perm.index("Bob")
                if child_perm[bob_pos] != "Timothy":
                    continue
            except ValueError:
                continue
            # Constraint 13: Meredith is in the sixth house
            if child_perm[5] != "Meredith":
                continue
            # Constraint 4: Samantha is not in the second house
            if child_perm[1] == "Samantha":
                continue

            for smoothie_perm in permutations(smoothies):
                # Constraint 7: Alice is the Watermelon smoothie lover
                if smoothie_perm[alice_name_pos] != "watermelon":
                    continue
                # Constraint 14: Dragonfruit is the child Meredith
                if smoothie_perm[child_perm.index("Meredith")] != "dragonfruit":
                    continue
                # Constraint 5: Watermelon is right of Cherry
                try:
                    cherry_pos = smoothie_perm.index("cherry")
                    watermelon_pos = smoothie_perm.index("watermelon")
                    if watermelon_pos <= cherry_pos:
                        continue
                except ValueError:
                    continue
                # Constraint 12: Cherry is directly left of Samantha
                try:
                    cherry_pos = smoothie_perm.index("cherry")
                    samantha_pos = child_perm.index("Samantha")
                    if cherry_pos + 1 != samantha_pos:
                        continue
                except ValueError:
                    continue
                # Constraint 1: Fred and Desert are next to each other
                fred_pos = child_perm.index("Fred")
                desert_pos = smoothie_perm.index("desert")
                if abs(fred_pos - desert_pos) != 1:
                    continue
                # Constraint 2: Blueberry is left of Fred
                blueberry_pos = smoothie_perm.index("blueberry")
                if blueberry_pos >= fred_pos:
                    continue
                # Constraint 3: Alice is not in the fifth house
                if name_perm[4] == "Alice":
                    continue
                # Constraint 8: Peter is right of Samantha
                samantha_pos = child_perm.index("Samantha")
                peter_pos = name_perm.index("Peter")
                if peter_pos <= samantha_pos:
                    continue

                # All constraints satisfied, build the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Smoothie"],
                        "rows": []
                    }
                }
                for i in range(6):
                    solution["solution"]["rows"].append([
                        str(i + 1),
                        name_perm[i],
                        child_perm[i],
                        smoothie_perm[i]
                    ])
                return solution

    return {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))