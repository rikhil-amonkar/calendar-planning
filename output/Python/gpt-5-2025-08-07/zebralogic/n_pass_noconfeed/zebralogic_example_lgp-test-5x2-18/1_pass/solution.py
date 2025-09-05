import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    solutions = []

    # Helper to get position (1-based) of a value in a house-ordered list
    def pos_of(house_list, value):
        return house_list.index(value) + 1

    # Generate possible children arrangements with fixed constraints:
    # 3) Fred is in the second house.
    # 7) Fred is directly left of Bella. -> Bella is in the third house.
    # This fixes: House 2 = Fred, House 3 = Bella
    fixed_children = [None] * 5
    fixed_children[1] = "Fred"   # house 2
    fixed_children[2] = "Bella"  # house 3

    remaining_children = ["Timothy", "Meredith", "Samantha"]
    remaining_positions = [0, 3, 4]  # houses 1, 4, 5

    for perm_children in itertools.permutations(remaining_children):
        child_at = fixed_children[:]
        for idx, pos in enumerate(remaining_positions):
            child_at[pos] = perm_children[idx]

        # 2) Timothy is somewhere to the left of Samantha.
        if not (pos_of(child_at, "Timothy") < pos_of(child_at, "Samantha")):
            continue

        # Names permutations with constraints
        for perm_names in itertools.permutations(names):
            name_at = list(perm_names)

            # 5) Eric is not in the third house.
            if name_at[2] == "Eric":
                continue
            # 6) Bob is not in the third house.
            if name_at[2] == "Bob":
                continue

            # Cross-attribute constraints:
            # 1) Bob is somewhere to the left of Samantha.
            if not (pos_of(name_at, "Bob") < pos_of(child_at, "Samantha")):
                continue

            # 4) There is one house between Alice and Samantha.
            if abs(pos_of(name_at, "Alice") - pos_of(child_at, "Samantha")) != 2:
                continue

            # 8) Samantha is somewhere to the left of Peter.
            if not (pos_of(child_at, "Samantha") < pos_of(name_at, "Peter")):
                continue

            solutions.append((name_at, child_at))

    if not solutions:
        raise RuntimeError("No solution found.")
    if len(solutions) > 1:
        # In case of multiple solutions, we still output the first deterministically.
        pass

    name_at, child_at = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": []
        }
    }

    for i in range(5):
        row = [str(i + 1), name_at[i], child_at[i]]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve()