import json
from itertools import permutations

def solve():
    # Input variables
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Fixed positions from direct clues
    fixed_name_pos = {
        "Eric": 6,    # Clue 6
        "Peter": 1,   # Clue 8
        "Carol": 5,   # Clue 7 (must be adjacent to Eric(6) -> only 5)
        "Bob": 3      # Clue 9
    }
    fixed_cigar_pos = {
        "blue master": 5,  # Clue 2
        "pall mall": 3     # Clue 5
    }

    remaining_name_houses = [h for h in houses if h not in fixed_name_pos.values()]
    remaining_names = [n for n in names if n not in fixed_name_pos]

    # Sanity check: Carol adjacent to Eric (Clue 7)
    assert abs(fixed_name_pos["Carol"] - fixed_name_pos["Eric"]) == 1

    solutions = []

    # Assign remaining names to remaining houses
    for name_perm in permutations(remaining_names):
        pos_name = fixed_name_pos.copy()
        for h, n in zip(remaining_name_houses, name_perm):
            pos_name[n] = h

        # Now assign cigars with constraints
        # Remaining cigars and houses
        remaining_cigar_houses = [h for h in houses if h not in fixed_cigar_pos.values()]
        remaining_cigars = [c for c in cigars if c not in fixed_cigar_pos]

        # We'll place blends and yellow monster first due to the distance constraint (Clue 4)
        # Then place prince and dunhill
        for blends_house in remaining_cigar_houses:
            # There must be exactly one house between yellow monster and blends
            ym_candidates = []
            if blends_house - 2 in remaining_cigar_houses:
                ym_candidates.append(blends_house - 2)
            if blends_house + 2 in remaining_cigar_houses:
                ym_candidates.append(blends_house + 2)

            for ym_house in ym_candidates:
                if ym_house == blends_house:
                    continue

                # Prepare cigar position dict
                pos_cigar = fixed_cigar_pos.copy()
                pos_cigar["blends"] = blends_house
                pos_cigar["yellow monster"] = ym_house

                # Remaining cigars now
                rem_cigars2 = [c for c in remaining_cigars if c not in ("blends", "yellow monster")]
                rem_houses2 = [h for h in remaining_cigar_houses if h not in (blends_house, ym_house)]

                # Enumerate assignments of the last two cigars (prince, dunhill)
                for cperm in permutations(rem_cigars2):
                    pos_cigar2 = pos_cigar.copy()
                    for h, c in zip(rem_houses2, cperm):
                        pos_cigar2[c] = h

                    # Check constraints involving Arnold (Clues 1 and 3)
                    arn_pos = pos_name["Arnold"]
                    if not (arn_pos < pos_cigar2["blends"]):
                        continue
                    if not (arn_pos < pos_cigar2["prince"]):
                        continue

                    # Clue 4 already enforced via construction

                    # All constraints satisfied; build solution rows
                    name_at_house = {v: k for k, v in pos_name.items()}
                    cigar_at_house = {v: k for k, v in pos_cigar2.items()}

                    rows = []
                    for h in houses:
                        rows.append([str(h), name_at_house[h], cigar_at_house[h]])

                    solutions.append({
                        "solution": {
                            "header": ["House", "Name", "Cigar"],
                            "rows": rows
                        }
                    })

    # Ensure at least one solution found
    if not solutions:
        raise ValueError("No solution found.")

    # If multiple solutions are found, pick the first (puzzles are expected to be unique)
    print(json.dumps(solutions[0], ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()