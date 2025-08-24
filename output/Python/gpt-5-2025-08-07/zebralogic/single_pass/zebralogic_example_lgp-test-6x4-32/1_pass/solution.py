import itertools
import json

def positions_of(arr):
    return {value: idx + 1 for idx, value in enumerate(arr)}

def constrained_permutations(items, fixed_item_to_pos):
    # items: list of all possible values in this category
    # fixed_item_to_pos: dict mapping item -> 1-based position
    # Returns generator of lists (length = len(items)) representing positions 1..n
    n = len(items)
    arr = [None] * n

    # Check for duplicate positions in fixed mapping (conflicts)
    occupied = {}
    for item, pos in fixed_item_to_pos.items():
        idx = pos - 1
        if idx < 0 or idx >= n:
            return  # invalid position, yield nothing
        if arr[idx] is not None and arr[idx] != item:
            return  # conflicting assignment
        arr[idx] = item
        if pos in occupied and occupied[pos] != item:
            return  # two different items assigned to same position
        occupied[pos] = item

    remaining_items = [i for i in items if i not in fixed_item_to_pos]
    remaining_positions = [i for i in range(n) if arr[i] is None]

    for perm in itertools.permutations(remaining_items):
        temp = arr[:]
        for pos_idx, item in zip(remaining_positions, perm):
            temp[pos_idx] = item
        yield temp

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    HouseStyles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    MusicGenres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    Hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    solutions = []

    # Music constraints:
    # 1. Rock in 5th house.
    # 11. Country in 1st house.
    music_fixed = {
        "rock": 5,
        "country": 1
    }

    for music_arr in constrained_permutations(MusicGenres, music_fixed):
        posM = positions_of(music_arr)

        # Early pruning: "jazz directly left of Eric" implies jazz cannot be at position 6 (needs right neighbor).
        if posM["jazz"] == 6:
            continue

        # Names constraints:
        # 15. Bob in the third house.
        names_fixed = {"Bob": 3}
        for names_arr in constrained_permutations(Names, names_fixed):
            posN = positions_of(names_arr)

            # 5. The person who loves jazz is directly left of Eric.
            if posM["jazz"] + 1 != posN["Eric"]:
                continue

            # 7. Carol is the person who loves hip-hop music.
            if posN["Carol"] != posM["hip hop"]:
                continue

            # Styles constraints with fixed equalities:
            # 8. Craftsman-style house is Arnold.
            # 9. Ranch-style home is Eric.
            # 3. Mediterranean-style is the person who loves hip-hop music.
            styles_fixed = {
                "craftsman": posN["Arnold"],
                "ranch": posN["Eric"],
                "mediterranean": posM["hip hop"]
            }

            # If any two styles are forced to the same house, skip
            if len(set(styles_fixed.values())) != len(styles_fixed.values()):
                continue

            for styles_arr in constrained_permutations(HouseStyles, styles_fixed):
                posS = positions_of(styles_arr)

                # 4. Two houses between Arnold and the person residing in a Victorian house.
                if abs(posN["Arnold"] - posS["victorian"]) != 3:
                    continue

                # Hobbies constraints with fixed equalities:
                # 10. Woodworking hobbyist is the person residing in a Victorian house.
                # 14. The person who enjoys gardening is Eric.
                # 13. Alice is the photography enthusiast.
                hobbies_fixed = {
                    "woodworking": posS["victorian"],
                    "gardening": posN["Eric"],
                    "photography": posN["Alice"]
                }
                # If any two hobbies are fixed to the same position (impossible), skip
                if len(set(hobbies_fixed.values())) != len(hobbies_fixed.values()):
                    continue

                for hobbies_arr in constrained_permutations(Hobbies, hobbies_fixed):
                    posH = positions_of(hobbies_arr)

                    # 2. The person who loves classical music and the woodworking hobbyist are next to each other.
                    if abs(posM["classical"] - posH["woodworking"]) != 1:
                        continue

                    # 6. The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
                    if not (posM["hip hop"] < posH["knitting"]):
                        continue

                    # 12. One house between the painter and the person living in a colonial-style house. (distance 2)
                    if abs(posH["painting"] - posS["colonial"]) != 2:
                        continue

                    # All constraints satisfied, construct solution
                    solution_rows = []
                    for h in houses:
                        solution_rows.append([
                            str(h),
                            names_arr[h - 1],
                            styles_arr[h - 1],
                            music_arr[h - 1],
                            hobbies_arr[h - 1]
                        ])
                    solutions.append({
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                            "rows": solution_rows
                        }
                    })
                    # If unique solution is expected, we can return immediately
                    return solutions[0]

    # If no solution found (should not happen with valid puzzle), return empty structure
    return {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": []
        }
    }

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))