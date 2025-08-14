#!/usr/bin/env python3
import json
import sys

# Global domains for each category
DOMAINS = {
    "Name": ["Bob", "Arnold", "Alice", "Peter", "Eric"],
    "hobby": ["cooking", "gardening", "painting", "photography", "knitting"],
    "sport": ["swimming", "tennis", "soccer", "baseball", "basketball"],
    "style": ["ranch", "craftsman", "victorian", "modern", "colonial"],
    "child": ["Timothy", "Samantha", "Bella", "Meredith", "Fred"],
    "height": ["average", "very tall", "very short", "short", "tall"]
}

# Local check for a candidate house (using 0-indexed house positions).
def local_valid(candidate, index, solution):
    # Forced positions:
    # House 2 (index 1) must be Alice, gardening, and tall.
    if index == 1:
        if candidate["Name"] != "Alice":
            return False
        if candidate["hobby"] != "gardening":
            return False
        if candidate["height"] != "tall":
            return False
    # House 5 (index 4) must have style "victorian"
    if index == 4:
        if candidate["style"] != "victorian":
            return False
    # If style is victorian, it must be house 5.
    if candidate["style"] == "victorian" and index != 4:
        return False

    # Clue 1 & 13: average height <-> child is Meredith (and craftsman <-> average)
    if candidate["height"] == "average" and candidate["child"] != "Meredith":
        return False
    if candidate["child"] == "Meredith" and candidate["height"] != "average":
        return False
    if candidate["style"] == "craftsman" and candidate["height"] != "average":
        return False

    # Clue 4: Alice is tall.
    if candidate["Name"] == "Alice" and candidate["height"] != "tall":
        return False

    # Clue 2: The person who is tall is in house 2 (already forced above).

    # Clue 3 and 16: Peter must be very tall and must be immediately left of the Victorian house.
    if candidate["Name"] == "Peter":
        # Peter can only appear in house #4 (index 3) so that house #5 (index 4) is Victorian.
        if index != 3:
            return False
        # Also, Peter must be very tall.
        if candidate["height"] != "very tall":
            return False
    # If sport is baseball then height must be very tall and vice versa
    if candidate["height"] == "very tall" and candidate["sport"] != "baseball":
        return False
    if candidate["sport"] == "baseball" and candidate["height"] != "very tall":
        return False

    # Clue 5 is covered by the above.

    # Clue 7: Bob paints.
    if candidate["Name"] == "Bob" and candidate["hobby"] != "painting":
        return False
    if candidate["hobby"] == "painting" and candidate["Name"] != "Bob":
        return False

    # Clue 10: The person who loves tennis has a child named Samantha.
    if candidate["sport"] == "tennis" and candidate["child"] != "Samantha":
        return False
    # Clue 12: The person whose child is Samantha lives in a modern style house.
    if candidate["child"] == "Samantha" and candidate["style"] != "modern":
        return False

    # Clue 19: The modern-style person’s hobby is cooking.
    if candidate["style"] == "modern" and candidate["hobby"] != "cooking":
        return False
    if candidate["hobby"] == "cooking" and candidate["style"] != "modern":
        return False

    # Clue 14: The person whose child is Fred lives in a Victorian house.
    if candidate["child"] == "Fred" and index != 4:
        return False

    # Clue 15: The person who is short must love basketball.
    if candidate["height"] == "short" and candidate["sport"] != "basketball":
        return False
    if candidate["sport"] == "basketball" and candidate["height"] != "short":
        return False

    # Clue 11: The person who loves soccer is not in the first house (index 0).
    if candidate["sport"] == "soccer" and index == 0:
        return False

    # Now cross-house neighbor constraints from already assigned houses:

    # Clue 3 neighbor: if the previous house was Peter then this candidate must have style "victorian".
    if index - 1 >= 0:
        prev = solution[index - 1]
        if prev["Name"] == "Peter":
            if candidate["style"] != "victorian":
                return False

    # Clue 6: The houses with child Meredith and the mother of Timothy must be next to each other.
    for i, house in enumerate(solution):
        if house["child"] == "Meredith" and candidate["child"] == "Timothy":
            if abs(index - i) != 1:
                return False
        if house["child"] == "Timothy" and candidate["child"] == "Meredith":
            if abs(index - i) != 1:
                return False

    # Clue 9: The person who is very short must be to the right of Eric.
    # If any house in the partial solution is Eric in the last position, it's already a violation.
    for i, house in enumerate(solution):
        if house["Name"] == "Eric" and i == 4:
            return False
    if candidate["Name"] == "Eric" and index == 4:
        return False

    # Clue 17: The ranch-style house must be to the left of the person who loves cooking.
    # (If a ranch house is already assigned, then any candidate with cooking must come later -- our assignment order is increasing.)
    # Since we assign houses in order, if a candidate has hobby "cooking", it is by Clue 19 coupled with modern.
    # We only check later in the full solution.

    # Clue 18: The person who enjoys knitting must be next to the one who enjoys gardening.
    # House 2 (index 1) is gardening, so one of its neighbors (index 0 or index 2) must be knitting.
    if index == 2:
        # At index 2, House1 (index 0) already assigned and House2 (index 1) is fixed
        if solution[1]["hobby"] == "gardening":
            if solution[0]["hobby"] != "knitting" and candidate["hobby"] != "knitting":
                return False
    # Otherwise, we defer the check when both neighbors of House2 are assigned.

    return True

# Full solution check (after all 5 houses are assigned)
def full_check(solution):
    # Re-check forced positions:
    if solution[1]["Name"] != "Alice" or solution[1]["hobby"] != "gardening" or solution[1]["height"] != "tall":
        return False
    if solution[4]["style"] != "victorian":
        return False

    # Clue 3: Peter must be in house 4 (index 3) and the house to its right must be victorian.
    for i, house in enumerate(solution):
        if house["Name"] == "Peter":
            if i != 3:
                return False
            if i+1 < len(solution) and solution[i+1]["style"] != "victorian":
                return False

    # Clue 6: The house with child Meredith and the house with child Timothy must be next to each other.
    idx_meredith = None
    idx_timothy = None
    for i, house in enumerate(solution):
        if house["child"] == "Meredith":
            idx_meredith = i
        if house["child"] == "Timothy":
            idx_timothy = i
    if idx_meredith is None or idx_timothy is None or abs(idx_meredith - idx_timothy) != 1:
        return False

    # Clue 9: The person who is very short must be to the right of Eric.
    idx_eric = None
    for i, house in enumerate(solution):
        if house["Name"] == "Eric":
            idx_eric = i
            break
    if idx_eric is not None:
        if idx_eric == 4:
            return False
        found = False
        for j in range(idx_eric+1, 5):
            if solution[j]["height"] == "very short":
                found = True
                break
        if not found:
            return False

    # Clue 17: The ranch-style house must be to the left of the person who loves cooking.
    idx_ranch = None
    idx_cooking = None
    for i, house in enumerate(solution):
        if house["style"] == "ranch":
            idx_ranch = i
        if house["hobby"] == "cooking":
            idx_cooking = i
    if (idx_ranch is None) or (idx_cooking is None) or (idx_ranch >= idx_cooking):
        return False

    # Clue 18: The knitting/gardening neighbors.
    # House2 (index 1) is gardening; so one of its neighbors (index 0 or index 2) must have hobby "knitting".
    if solution[1]["hobby"] == "gardening":
        neigh0 = solution[0]["hobby"]
        neigh2 = solution[2]["hobby"]
        if neigh0 != "knitting" and neigh2 != "knitting":
            return False

    return True

# Backtracking search.
def backtrack(index, solution, used):
    if index == 5:
        if full_check(solution):
            return solution
        else:
            return None

    for name in DOMAINS["Name"]:
        if name in used["Name"]:
            continue
        # Forced: House2 (index 1) must be Alice.
        if index == 1 and name != "Alice":
            continue
        # Peter can only appear in house 4 (index 3).
        if name == "Peter" and index != 3:
            continue

        for hobby in DOMAINS["hobby"]:
            if hobby in used["hobby"]:
                continue
            if index == 1 and hobby != "gardening":
                continue

            for sport in DOMAINS["sport"]:
                if sport in used["sport"]:
                    continue

                for style in DOMAINS["style"]:
                    if style in used["style"]:
                        continue
                    if index == 4 and style != "victorian":
                        continue
                    if style == "victorian" and index != 4:
                        continue

                    for child in DOMAINS["child"]:
                        if child in used["child"]:
                            continue

                        for height in DOMAINS["height"]:
                            if height in used["height"]:
                                continue

                            candidate = {
                                "House": str(index + 1),
                                "Name": name,
                                "hobby": hobby,
                                "sport": sport,
                                "style": style,
                                "child": child,
                                "height": height
                            }
                            if not local_valid(candidate, index, solution):
                                continue

                            # Add candidate to solution.
                            solution.append(candidate)
                            used["Name"].add(name)
                            used["hobby"].add(hobby)
                            used["sport"].add(sport)
                            used["style"].add(style)
                            used["child"].add(child)
                            used["height"].add(height)

                            result = backtrack(index + 1, solution, used)
                            if result is not None:
                                return result

                            # Backtrack: remove candidate and update used sets.
                            solution.pop()
                            used["Name"].remove(name)
                            used["hobby"].remove(hobby)
                            used["sport"].remove(sport)
                            used["style"].remove(style)
                            used["child"].remove(child)
                            used["height"].remove(height)
    return None

def main():
    # Initialize empty solution and used sets for each category.
    solution = []
    used = {
        "Name": set(),
        "hobby": set(),
        "sport": set(),
        "style": set(),
        "child": set(),
        "height": set()
    }
    sol = backtrack(0, solution, used)
    if sol is None:
        result = {"solution": {"header": [], "rows": []}}
    else:
        # Map internal keys to output header keys:
        header = ["House", "Name", "hobby", "favorite sport", "house style", "child", "height"]
        rows = []
        # Ensure houses are in order (they were added in order 0..4)
        for house in sol:
            row = [
                house["House"],
                house["Name"],
                house["hobby"],
                house["sport"],
                house["style"],
                house["child"],
                house["height"]
            ]
            rows.append(row)
        result = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    sys.exit(main())