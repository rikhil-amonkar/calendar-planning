import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]

    # We will assign:
    # - name_at[house] = name
    # - child_at[house] = child

    solutions = []

    # Pre-place children based on direct constraints:
    # 3. Fred is in the second house.
    # 7. Fred is directly left of Bella => Bella is in the third house.
    fixed_children = {2: "Fred", 3: "Bella"}
    remaining_children = [c for c in children if c not in fixed_children.values()]
    remaining_positions = [h for h in houses if h not in fixed_children.keys()]  # [1,4,5]

    # Iterate over all permutations for remaining children on remaining positions
    for perm in itertools.permutations(remaining_children):
        child_at = dict(fixed_children)
        for h, c in zip(remaining_positions, perm):
            child_at[h] = c

        # Build inverse mapping: pos_of_child[child] = house
        pos_of_child = {c: h for h, c in child_at.items()}

        # Apply child-only constraints:
        # 2. Mother of Timothy is somewhere to the left of mother of Samantha.
        if not (pos_of_child["Timothy"] < pos_of_child["Samantha"]):
            continue

        # Now assign names
        for name_perm in itertools.permutations(names):
            name_at = {h: n for h, n in zip(houses, name_perm)}

            # Apply immediate constraints:
            # 5. Eric is not in the third house.
            if name_at[3] == "Eric":
                continue
            # 6. Bob is not in the third house.
            if name_at[3] == "Bob":
                continue

            # 4. There is one house between Alice and Samantha.
            if abs(houses.index(next(h for h in houses if name_at[h] == "Alice")) - houses.index(pos_of_child["Samantha"])) != 2:
                continue

            # 1. Bob is to the left of the person whose child is Samantha.
            if not (next(h for h in houses if name_at[h] == "Bob") < pos_of_child["Samantha"]):
                continue

            # 8. The person whose child is Samantha is to the left of Peter.
            if not (pos_of_child["Samantha"] < next(h for h in houses if name_at[h] == "Peter")):
                continue

            # All constraints satisfied; store solution
            solution_rows = []
            for h in houses:
                solution_rows.append([str(h), name_at[h], child_at[h]])
            solutions.append(solution_rows)

    # Ensure unique solution
    assert len(solutions) == 1, f"Expected exactly one solution, found {len(solutions)}"
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))