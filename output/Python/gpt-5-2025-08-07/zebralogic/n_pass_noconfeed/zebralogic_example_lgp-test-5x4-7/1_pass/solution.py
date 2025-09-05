import itertools
import json

def solve_puzzle():
    # Houses numbered 1..5 from left to right; we use 0-based indices internally.
    houses = [0, 1, 2, 3, 4]

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    Animals = ["horse", "dog", "bird", "fish", "cat"]
    Nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    solutions = []

    # Helper to get index of a value in an assigned array
    def pos_of(arr, val):
        return arr.index(val)

    # Generate animal arrangements with fixed constraints:
    # - The person who keeps horses is in the third house (index 2).
    # - The bird keeper is somewhere to the right of the cat lover.
    for perm_anim_rest in itertools.permutations([a for a in Animals if a != "horse"]):
        animal = [None] * 5
        animal[2] = "horse"  # Clue 11

        # Fill remaining positions [0,1,3,4] with the permutation
        rest_positions = [0, 1, 3, 4]
        for idx, pos in enumerate(rest_positions):
            animal[pos] = perm_anim_rest[idx]

        # Clue 4: The bird keeper is somewhere to the right of the cat lover.
        if pos_of(animal, "bird") <= pos_of(animal, "cat"):
            continue

        # Proceed to smoothies with constraints:
        # - The dog owner is directly left of the person who drinks Lime smoothies. (Clue 5)
        # - The Desert smoothie lover is the dog owner. (Clue 10)
        # - The bird keeper is the Watermelon smoothie lover. (Clue 9)
        dog_pos = pos_of(animal, "dog")
        bird_pos = pos_of(animal, "bird")

        # Dog must not be at the last house to have someone on the right for lime
        if dog_pos == 4:
            continue

        smoothie = [None] * 5
        smoothie[dog_pos] = "desert"        # Clue 10
        smoothie[dog_pos + 1] = "lime"      # Clue 5
        if bird_pos == dog_pos or bird_pos == dog_pos + 1:
            # Would conflict with "desert" or "lime"
            continue
        smoothie[bird_pos] = "watermelon"   # Clue 9

        # Fill remaining smoothie slots with remaining values
        assigned = {smoothie[p] for p in range(5) if smoothie[p] is not None}
        remaining_smoothies = [s for s in Smoothies if s not in assigned]
        remaining_positions = [i for i in range(5) if smoothie[i] is None]

        # Cherry cannot be at the last house (no one to its right for Peter), but this will be checked later with names.
        # However, we can still assign it here but ensure later "cherry" is not at index 4 if Peter isn't at 5.
        for perm_sm_rest in itertools.permutations(remaining_smoothies):
            s = smoothie[:]
            ok = True
            for idx, pos in enumerate(remaining_positions):
                s[pos] = perm_sm_rest[idx]

            # Optional prune: Cherry cannot be at index 4? Actually allowed if Peter at 5.
            # We'll defer the check to names stage.

            # Proceed to nationalities:
            # - The Dane is the person who keeps horses. (Clue 3)
            # - The Swedish person is directly left of the dog owner. (Clue 1)
            # - There are two houses between the dog owner and the British person. (Clue 2)
            nation = [None] * 5
            nation[pos_of(animal, "horse")] = "dane"  # Clue 3 (with Clue 11 already used)

            # Swede must be directly left of dog owner (Clue 1), so dog_pos cannot be 0
            if dog_pos == 0:
                continue
            nation[dog_pos - 1] = "swede"

            # Brit must be 3 apart from dog owner (Clue 2)
            possible_brit_positions = []
            if dog_pos + 3 <= 4:
                possible_brit_positions.append(dog_pos + 3)
            if dog_pos - 3 >= 0:
                possible_brit_positions.append(dog_pos - 3)
            # We'll assign brit later while iterating permutations; but we can prune:
            if not possible_brit_positions:
                continue

            remaining_nations = [n for n in Nationalities if n not in nation]
            remaining_positions_n = [i for i in range(5) if nation[i] is None]

            # Iterate over permutations of remaining nationalities with pruning for Brit position
            for perm_nat_rest in itertools.permutations(remaining_nations):
                n = nation[:]
                ok_nat = True
                for idx, pos in enumerate(remaining_positions_n):
                    n[pos] = perm_nat_rest[idx]

                # Check Brit constraint now (Clue 2)
                if abs(pos_of(n, "brit") - dog_pos) != 3:
                    continue

                # Proceed to names:
                # - Eric is the cat lover. (Clue 6)
                # - Bob is the bird keeper. (Clue 7)
                # - The Norwegian is Alice. (Clue 12)
                name = [None] * 5
                name[pos_of(animal, "cat")] = "Eric"       # Clue 6
                name[pos_of(animal, "bird")] = "Bob"       # Clue 7
                name[pos_of(n, "norwegian")] = "Alice"     # Clue 12

                # If any conflicts in names (duplicate assignment to same position), skip
                assigned_names = [nm for nm in name if nm is not None]
                if len(set(assigned_names)) != len(assigned_names):
                    continue

                remaining_names = [nm for nm in Names if nm not in assigned_names]
                remaining_positions_name = [i for i in range(5) if name[i] is None]

                for perm_names_rest in itertools.permutations(remaining_names):
                    nm = name[:]
                    for idx, pos in enumerate(remaining_positions_name):
                        nm[pos] = perm_names_rest[idx]

                    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
                    cherry_pos = pos_of(s, "cherry")
                    if cherry_pos == 4:
                        # No house to the right
                        continue
                    if nm[cherry_pos + 1] != "Peter":
                        continue

                    # All constraints satisfied; record solution
                    solution = {
                        "animal": animal[:],
                        "smoothie": s[:],
                        "nation": n[:],
                        "name": nm[:],
                    }
                    solutions.append(solution)

    # Expect exactly one solution
    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple, choose the first (shouldn't happen for a well-posed puzzle)
    sol = solutions[0]

    # Build JSON output
    header = ["House", "Name", "Smoothie", "Animal", "Nationality"]
    rows = []
    for i in range(5):
        # Houses are 1-indexed in output
        rows.append([
            str(i + 1),
            sol["name"][i],
            sol["smoothie"][i],
            sol["animal"][i],
            sol["nation"][i],
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))