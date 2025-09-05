import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Initialize structures (0-based indices for houses)
    name_at_house = [None] * 6
    cigar_at_house = [None] * 6

    # Apply fixed constraints from clues:
    # 8. Peter is in the first house.
    name_at_house[0] = "Peter"
    # 6. Eric is in the sixth house.
    name_at_house[5] = "Eric"
    # 9. Bob is in the third house.
    name_at_house[2] = "Bob"
    # 7. Carol and Eric are next to each other. With Eric at 6, Carol must be at 5.
    name_at_house[4] = "Carol"

    # 2. Blue Master in the fifth house.
    cigar_at_house[4] = "blue master"
    # 5. Pall Mall in the third house.
    cigar_at_house[2] = "pall mall"

    # Remaining names to place in houses 2 and 4 (indices 1 and 3): Alice, Arnold
    remaining_name_houses = [1, 3]
    remaining_names = ["Alice", "Arnold"]

    # Remaining cigars to place in houses 1,2,4,6 (indices 0,1,3,5)
    remaining_cigar_houses = [0, 1, 3, 5]
    remaining_cigars = [c for c in cigars if c not in ["blue master", "pall mall"]]

    def check_all_constraints(nah, cah):
        # Build index maps
        name_pos = {n: i for i, n in enumerate(nah) if n is not None}
        cigar_pos = {c: i for i, c in enumerate(cah) if c is not None}

        # Clue 2: Blue Master in the fifth house (index 4)
        if cah[4] is not None and cah[4] != "blue master":
            return False
        # Clue 5: Pall Mall in the third house (index 2)
        if cah[2] is not None and cah[2] != "pall mall":
            return False
        # Clue 6: Eric in sixth house (index 5)
        if nah[5] is not None and nah[5] != "Eric":
            return False
        # Clue 8: Peter in first house (index 0)
        if nah[0] is not None and nah[0] != "Peter":
            return False
        # Clue 9: Bob in third house (index 2)
        if nah[2] is not None and nah[2] != "Bob":
            return False
        # Clue 7: Carol and Eric are next to each other
        if "Carol" in name_pos and "Eric" in name_pos:
            if abs(name_pos["Carol"] - name_pos["Eric"]) != 1:
                return False
        # Clue 1: Arnold is somewhere to the left of the blends smoker.
        if "Arnold" in name_pos and "blends" in cigar_pos:
            if not (name_pos["Arnold"] < cigar_pos["blends"]):
                return False
        # Clue 3: Arnold is somewhere to the left of the Prince smoker.
        if "Arnold" in name_pos and "prince" in cigar_pos:
            if not (name_pos["Arnold"] < cigar_pos["prince"]):
                return False
        # Clue 4: One house between Yellow Monster and blends (difference of 2)
        if "yellow monster" in cigar_pos and "blends" in cigar_pos:
            if abs(cigar_pos["yellow monster"] - cigar_pos["blends"]) != 2:
                return False

        return True

    solutions = []

    # Assign the two remaining names to houses 2 and 4
    for name_perm in itertools.permutations(remaining_names, len(remaining_names)):
        nah = name_at_house[:]
        for h_idx, n in zip(remaining_name_houses, name_perm):
            nah[h_idx] = n

        # Quick check: ensure all names assigned
        if any(v is None for v in nah):
            continue

        # Now assign cigars to remaining houses
        for cigar_perm in itertools.permutations(remaining_cigars, len(remaining_cigar_houses)):
            cah = cigar_at_house[:]
            valid = True
            for h_idx, c in zip(remaining_cigar_houses, cigar_perm):
                cah[h_idx] = c

            # Check all constraints
            if not check_all_constraints(nah, cah):
                valid = False

            if valid:
                solutions.append((nah, cah))

    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple, pick the first (the constraints should yield a unique solution)
    nah, cah = solutions[0]

    # Prepare output
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": []
        }
    }
    for i in range(6):
        result["solution"]["rows"].append([str(i + 1), nah[i], cah[i]])

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))