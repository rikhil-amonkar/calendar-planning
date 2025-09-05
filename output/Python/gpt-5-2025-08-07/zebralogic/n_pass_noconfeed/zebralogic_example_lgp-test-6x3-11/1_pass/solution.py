import json
import itertools

def solve_puzzle():
    houses = list(range(6))  # indices 0..5 correspond to houses 1..6

    Names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    HairColors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    Heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Constraints (encoded)
    # Fixed house constraints:
    house_index_alice = 3  # Alice is in 4th house (index 3)
    gray_house_index = 2   # Gray hair is in 3rd house (index 2)
    very_short_house_index = 4  # Very short is in 5th house (index 4)
    tall_house_index = 5        # Tall is in 6th house (index 5)

    # Useful lookups
    def idx_of(name, placement):
      return placement.index(name)

    # Iterate over all name assignments to houses
    for names_by_house in itertools.permutations(Names):
        # Constraint: Alice is in the fourth house
        if names_by_house[house_index_alice] != "Alice":
            continue

        # Using clues 1 + 8: Carol is directly left of Bob
        try:
            idx_carol = names_by_house.index("Carol")
            idx_bob = names_by_house.index("Bob")
        except ValueError:
            continue
        if idx_carol + 1 != idx_bob:
            continue

        # From clue 6 + 9 + 12: Eric (red hair) must be in house 1 or 5 (index 0 or 4)
        idx_eric = names_by_house.index("Eric")
        if idx_eric not in (0, 4):
            continue

        # From clue 3 and fixed house heights: Arnold is short, so Arnold cannot be in house 5 (very short) nor house 6 (tall)
        idx_arnold = names_by_house.index("Arnold")
        if idx_arnold in (very_short_house_index, tall_house_index):
            continue

        # Hair assignment with constraints
        hair_by_house = [None] * 6

        # Fixed: gray hair is in the third house (index 2)
        hair_by_house[gray_house_index] = "gray"

        # Bob has brown hair (clue 11)
        hair_by_house[idx_bob] = "brown"

        # Eric has red hair (clue 6) and abs(pos(gray) - pos(red)) = 2 (clue 9)
        hair_by_house[idx_eric] = "red"
        if abs(gray_house_index - idx_eric) != 2:
            continue

        # Carol has blonde hair (clue 8)
        hair_by_house[idx_carol] = "blonde"

        # Black hair is not in the fourth house (index 3) (clue 5)
        # Fill remaining hair colors
        assigned_colors = {c for c in hair_by_house if c is not None}
        remaining_colors = [c for c in HairColors if c not in assigned_colors]
        remaining_indices = [i for i, c in enumerate(hair_by_house) if c is None]

        valid_hair = None
        for perm in itertools.permutations(remaining_colors):
            candidate = hair_by_house[:]
            ok = True
            for idx, color in zip(remaining_indices, perm):
                if idx == 3 and color == "black":
                    ok = False
                    break
                candidate[idx] = color
            if not ok:
                continue
            # Double-check uniqueness
            if len(set(candidate)) == 6:
                valid_hair = candidate
                break

        if valid_hair is None:
            continue

        # Heights assignment with constraints
        heights_by_house = [None] * 6

        # Fixed per clues:
        heights_by_house[tall_house_index] = "tall"             # Clue 4
        heights_by_house[very_short_house_index] = "very short" # Clue 10

        # Arnold is short (clue 3)
        heights_by_house[idx_arnold] = "short"

        # Carol is very tall (clue 13 - blonde is very tall and Carol is blonde)
        heights_by_house[idx_carol] = "very tall"

        # Remaining heights are "average" and "super tall"
        assigned_heights = {h for h in heights_by_house if h is not None}
        remaining_heights = [h for h in Heights if h not in assigned_heights]
        remaining_indices_h = [i for i, h in enumerate(heights_by_house) if h is None]

        found_heights = None
        for perm in itertools.permutations(remaining_heights):
            candidate_h = heights_by_house[:]
            for idx, h in zip(remaining_indices_h, perm):
                candidate_h[idx] = h

            # Clue 7: super tall is somewhere to the right of average
            idx_avg = candidate_h.index("average")
            idx_super = candidate_h.index("super tall")
            if idx_super > idx_avg:
                found_heights = candidate_h
                break

        if found_heights is None:
            continue

        # Final consistency check for clue 1 (redundant due to names but kept for safety):
        # Blonde (Carol) is directly left of Bob
        if not (idx_carol + 1 == idx_bob and valid_hair[idx_carol] == "blonde"):
            continue

        # Build solution rows
        rows = []
        for i in range(6):
            house_num_str = str(i + 1)
            rows.append([house_num_str, names_by_house[i], valid_hair[i], found_heights[i]])

        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": rows
            }
        }
        return solution

    return None

def main():
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()