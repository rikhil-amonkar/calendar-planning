import json
import itertools

def solve_puzzle():
    # Houses numbered 1..5 (indices 0..4)
    houses = [1, 2, 3, 4, 5]

    # Attributes
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    # Helper to check adjacency
    def are_adjacent(pos1, pos2):
        return abs(pos1 - pos2) == 1

    solutions = []

    # Pre-constraints based on clues:
    #  - Dragonfruit at house 2 (index 1)
    #  - Watermelon at house 3 (index 2)
    #  - Desert not at house 5 (index 4)
    #  - Alice at house 3 (index 2)
    #  - Alice is Norwegian
    #  - Swede is left of Dragonfruit -> Swede at house 1 (index 0) because Dragonfruit is at house 2
    #  - Bob is the Dane
    #  - Dane next to Brit
    #  - Lime is 3 houses away from Dane
    #  - Peter not in house 1
    #  - Dragonfruit is left of Eric -> with dragonfruit at house 2, Eric must be in 3,4,5; but house 3 is Alice -> Eric in 4 or 5

    # Iterate over possible name assignments (permutations) with constraints
    for name_perm in itertools.permutations(names):
        # Alice in house 3
        if name_perm[2] != "Alice":
            continue
        # Peter not in house 1
        if name_perm[0] == "Peter":
            continue
        # Eric must be to the right of house 2 (house index > 1)
        if name_perm.index("Eric") <= 1:
            continue
        # Bob cannot be in house 1 or 3 because those are Swede and Norwegian respectively (cannot be Dane there)
        if name_perm[0] == "Bob" or name_perm[2] == "Bob":
            continue

        # Nationality assignment with constraints
        # Initialize nationalities with known fixed positions
        # house 1 -> swede, house 3 -> norwegian, house of Bob -> dane
        nat = [None] * 5
        nat[0] = "swede"
        nat[2] = "norwegian"
        bob_pos = name_perm.index("Bob")
        nat[bob_pos] = "dane"

        # Brit must be adjacent to Dane
        neighbors = []
        if bob_pos - 1 >= 0:
            neighbors.append(bob_pos - 1)
        if bob_pos + 1 < 5:
            neighbors.append(bob_pos + 1)

        # Try placing Brit at one of the valid neighbor positions not already assigned
        nat_possibilities = []
        for brit_pos in neighbors:
            if nat[brit_pos] is None:
                n = nat.copy()
                n[brit_pos] = "brit"
                # Remaining unassigned house gets 'german'
                remaining_indices = [i for i, v in enumerate(n) if v is None]
                if len(remaining_indices) == 1:
                    n[remaining_indices[0]] = "german"
                else:
                    # If more than one remains unassigned (shouldn't happen here), skip
                    continue
                nat_possibilities.append(n)

        for nat_assign in nat_possibilities:
            # Smoothie assignment with constraints
            sm = [None] * 5
            # Fixed smoothies
            sm[1] = "dragonfruit"
            sm[2] = "watermelon"

            # Remaining smoothies to place on houses [0,3,4]
            remaining_positions = [0, 3, 4]
            remaining_smoothies = ["desert", "lime", "cherry"]

            for sm_perm in itertools.permutations(remaining_smoothies):
                sm_trial = sm.copy()
                valid = True
                # Apply permutation
                for pos, s in zip(remaining_positions, sm_perm):
                    sm_trial[pos] = s
                # Desert not in house 5 (index 4)
                if sm_trial[4] == "desert":
                    valid = False
                if not valid:
                    continue

                # Lime is 3 houses away from Dane
                lime_pos = sm_trial.index("lime")
                dane_pos = nat_assign.index("dane")
                if abs(lime_pos - dane_pos) != 3:
                    continue

                # Dragonfruit (house 2) left of Eric
                eric_pos = name_perm.index("Eric")
                if not (1 < eric_pos):  # house index of Eric must be > 1 (house > 2)
                    continue

                # All constraints satisfied, record solution
                solution = []
                for i in range(5):
                    solution.append({
                        "House": str(i + 1),
                        "Name": name_perm[i],
                        "Smoothie": sm_trial[i],
                        "Nationality": nat_assign[i],
                    })
                solutions.append(solution)

    # Prefer a unique solution; if multiple, take the first
    if not solutions:
        raise ValueError("No solution found.")
    final = solutions[0]

    # Build JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": [[row["House"], row["Name"], row["Smoothie"], row["Nationality"]] for row in final]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))