import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ["Arnold", "Peter", "Eric", "Alice"]
    HouseStyles = ["craftsman", "colonial", "victorian", "ranch"]
    HairColors = ["red", "blonde", "black", "brown"]
    Children = ["Bella", "Fred", "Meredith", "Samantha"]
    BookGenres = ["mystery", "fantasy", "romance", "science fiction"]

    solutions = []

    # Fixed constraints derived directly from clues:
    # 1. Craftsman is in the third house.
    craftsman_pos = 3
    # 9. Black hair is in the second house.
    black_pos = 2
    # 3. Brown hair is in the fourth house.
    brown_pos = 4
    # 4. Samantha is in the fourth house.
    samantha_pos = 4
    # 12. The person who has black hair is Eric. => Eric is in house 2.
    eric_pos = 2

    # We will iterate possible positions for Arnold, Peter, Alice given Eric=2.
    remaining_positions = [p for p in houses if p != eric_pos]  # [1,3,4]
    for arnold_pos, peter_pos, alice_pos in permutations(remaining_positions, 3):
        # 7. Arnold has red hair. So red hair at arnold_pos.
        red_pos = arnold_pos

        # Quick consistency checks with fixed hair colors
        if red_pos == black_pos:
            continue  # Can't have both red and black at same house
        if red_pos == brown_pos:
            continue  # Can't have red and brown at same house

        # 8. Alice lives in a colonial-style house.
        # 1. Craftsman is at house 3, so Alice cannot be at 3 (since she is colonial).
        if alice_pos == craftsman_pos:
            continue

        # 10. Peter loves fantasy books --> just a mapping; but check child clue with house 4:
        # 6. Peter's child is Bella, and 4. house4 child is Samantha; thus Peter cannot be in house 4.
        if peter_pos == samantha_pos:
            continue

        # Hair mapping determined:
        hair_by_pos = {1: None, 2: "black", 3: None, 4: "brown"}
        hair_by_pos[red_pos] = "red"
        # Assign remaining hair "blonde" to the only house left without a hair color
        remaining_hair_positions = [p for p in houses if hair_by_pos[p] is None]
        if len(remaining_hair_positions) != 1:
            continue
        hair_by_pos[remaining_hair_positions[0]] = "blonde"

        # Children mapping:
        # 6. Peter -> Bella
        # 11. Arnold -> Meredith
        # 4. House 4 -> Samantha
        child_by_pos = {1: None, 2: None, 3: None, 4: "Samantha"}
        # Check conflicts: if Peter is at 4 (already checked), or Arnold at 4 conflicts with Samantha
        if arnold_pos == 4:
            continue  # Arnold's child is Meredith, not Samantha
        child_by_pos[peter_pos] = "Bella"
        child_by_pos[arnold_pos] = "Meredith"
        # Remaining child is Fred
        remaining_child_positions = [p for p in houses if child_by_pos[p] is None]
        if len(remaining_child_positions) != 1:
            continue
        child_by_pos[remaining_child_positions[0]] = "Fred"

        # Books mapping:
        # 2. Alice -> romance
        # 10. Peter -> fantasy
        # 13. Arnold -> science fiction
        # Remaining -> mystery (Eric)
        book_by_pos = {1: None, 2: None, 3: None, 4: None}
        book_by_pos[alice_pos] = "romance"
        book_by_pos[peter_pos] = "fantasy"
        book_by_pos[arnold_pos] = "science fiction"
        remaining_book_positions = [p for p in houses if book_by_pos[p] is None]
        if len(remaining_book_positions) != 1:
            continue
        book_by_pos[remaining_book_positions[0]] = "mystery"

        # Styles mapping:
        # 1. craftsman at 3
        # 8. Alice -> colonial
        style_by_pos = {1: None, 2: None, 3: "craftsman", 4: None}
        if style_by_pos[alice_pos] is not None and style_by_pos[alice_pos] != "craftsman":
            # In case of pre-set style at alice_pos (shouldn't be except pos 3), skip
            pass
        # Assign colonial to Alice's house
        if alice_pos == 3:
            continue  # already checked above but keep safe
        style_by_pos[alice_pos] = "colonial"

        # Remaining styles: victorian, ranch to remaining two positions
        remaining_positions_for_style = [p for p in houses if style_by_pos[p] is None]
        remaining_styles = ["victorian", "ranch"]

        valid_style_assignment_found = False
        for s1, s2 in permutations(remaining_styles, 2):
            temp_style = style_by_pos.copy()
            temp_style[remaining_positions_for_style[0]] = s1
            temp_style[remaining_positions_for_style[1]] = s2

            # 5. ranch is somewhere to the right of red hair (Arnold)
            ranch_pos = [p for p, st in temp_style.items() if st == "ranch"][0]
            if ranch_pos > red_pos:
                # All constraints satisfied so far
                style_by_pos = temp_style
                valid_style_assignment_found = True
                break

        if not valid_style_assignment_found:
            continue

        # Name mapping to positions
        name_by_pos = {arnold_pos: "Arnold", peter_pos: "Peter", eric_pos: "Eric", alice_pos: "Alice"}

        # Final validation: ensure each category is unique per house
        if len(set(name_by_pos.values())) != 4:
            continue
        if len(set(style_by_pos.values())) != 4:
            continue
        if len(set(hair_by_pos.values())) != 4:
            continue
        if len(set(child_by_pos.values())) != 4:
            continue
        if len(set(book_by_pos.values())) != 4:
            continue

        # Construct solution rows in house order 1..4
        rows = []
        for pos in houses:
            rows.append([
                str(pos),
                name_by_pos[pos],
                style_by_pos[pos],
                hair_by_pos[pos],
                child_by_pos[pos],
                book_by_pos[pos],
            ])

        solutions.append(rows)

    # Expect a unique solution
    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple solutions, pick the first (shouldn't happen for a well-posed puzzle)
    final_rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": final_rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))