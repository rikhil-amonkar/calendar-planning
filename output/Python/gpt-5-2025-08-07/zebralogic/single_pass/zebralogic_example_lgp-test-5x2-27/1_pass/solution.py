import itertools
import json

def solve_puzzle():
    # Houses indexed 0..4 represent houses 1..5
    houses = list(range(5))

    # Attributes
    names_all = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights_all = ["very tall", "average", "tall", "very short", "short"]

    solutions = []

    # Constraint setup from clues:
    # 1) short is in the second house -> index 1
    # 7) average is in the fifth house -> index 4
    # 5) Alice is directly left of average -> implies Alice at index 3 (house 4)
    fixed_name_at_index = {3: "Alice"}  # index 3 (house 4)
    fixed_height_at_index = {1: "short", 4: "average"}  # house 2 and house 5

    # Generate name assignments with Alice fixed at 4th house (index 3)
    remaining_names = [n for n in names_all if n != "Alice"]
    for perm in itertools.permutations(remaining_names):
        names = [None] * 5
        names[3] = "Alice"
        fill_indices = [0, 1, 2, 4]
        for idx, name in zip(fill_indices, perm):
            names[idx] = name

        # Clue 2: Peter is directly left of Bob
        p_idx = names.index("Peter")
        b_idx = names.index("Bob")
        if b_idx != p_idx + 1:
            continue

        # Clue 3: Eric is somewhere to the left of Peter
        if names.index("Eric") >= p_idx:
            continue

        # Heights assignment under constraints
        # Initialize with fixed heights
        base_heights = [None] * 5
        base_heights[1] = "short"     # Clue 1
        base_heights[4] = "average"   # Clue 7

        # Clue 4: very tall is directly left of Peter -> position p_idx - 1
        vt_pos = p_idx - 1
        if vt_pos < 0:
            continue
        # Check conflict with fixed heights
        if base_heights[vt_pos] is not None and base_heights[vt_pos] != "very tall":
            continue
        if vt_pos in (1, 4):
            # These are fixed to short/average; cannot be very tall
            continue
        heights = base_heights[:]
        heights[vt_pos] = "very tall"

        # Clue 6: short (index 1) and very short are next to each other -> very short at 0 or 2
        possible_vs_positions = [pos for pos in (0, 2) if heights[pos] is None]
        if not possible_vs_positions:
            continue

        for vs_pos in possible_vs_positions:
            h = heights[:]
            h[vs_pos] = "very short"

            # Remaining height must be "tall"
            remaining_height = list(set(heights_all) - set([x for x in h if x is not None]))
            if len(remaining_height) != 1 or remaining_height[0] != "tall":
                continue
            # Fill the last None with "tall"
            for i in range(5):
                if h[i] is None:
                    h[i] = "tall"

            # Final validation of all clues (some already enforced):
            # 1) short is in the second house
            if h[1] != "short":
                continue
            # 2) Peter directly left of Bob -> already checked
            # 3) Eric left of Peter -> already checked
            # 4) very tall directly left of Peter -> enforced
            # 5) Alice directly left of average -> Alice at 3 and average at 4 enforced
            if not (names[3] == "Alice" and h[4] == "average"):
                continue
            # 6) short and very short are next to each other
            if abs(h.index("very short") - 1) != 1:
                continue
            # 7) average at fifth house -> enforced

            solutions.append((names, h))

    assert len(solutions) == 1, f"Expected a unique solution, found {len(solutions)}"
    names_sol, heights_sol = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": [
                [str(i + 1), names_sol[i], heights_sol[i]] for i in range(5)
            ]
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))