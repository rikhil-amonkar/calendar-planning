import json
from itertools import permutations

def solve_puzzle():
    # Attributes
    houses = [0, 1, 2, 3, 4]  # 0-based indexing for positions
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    solution = None

    # Iterate over all permutations for names
    for name_at in permutations(names):
        # Clue 10: Alice is in the third house (index 2)
        if name_at[2] != "Alice":
            continue
        # Clue 3: Peter is not in the first house
        if name_at[0] == "Peter":
            continue

        # Precompute positions for names
        pos_name = {n: i for i, n in enumerate(name_at)}

        # Iterate over all permutations for smoothies
        for smoothie_at in permutations(smoothies):
            # Clue 2: Dragonfruit is in the second house (index 1)
            if smoothie_at[1] != "dragonfruit":
                continue
            # Clue 11: Watermelon is in the third house (index 2)
            if smoothie_at[2] != "watermelon":
                continue
            # Clue 5: Desert not in the fifth house (index 4)
            if smoothie_at[4] == "desert":
                continue
            # Clue 1: Dragonfruit lover is to the left of Eric
            if not (1 < pos_name["Eric"]):
                continue

            # Precompute positions for smoothies
            pos_smoothie = {s: i for i, s in enumerate(smoothie_at)}

            # Iterate over all permutations for nationalities
            for nat_at in permutations(nationalities):
                pos_nat = {n: i for i, n in enumerate(nat_at)}

                # Clue 4: Dane and Brit are next to each other
                if abs(pos_nat["dane"] - pos_nat["brit"]) != 1:
                    continue
                # Clue 8: Bob is the Dane
                if pos_name["Bob"] != pos_nat["dane"]:
                    continue
                # Clue 9: Alice is the Norwegian
                if pos_name["Alice"] != pos_nat["norwegian"]:
                    continue
                # Clue 6: Swede is left of Dragonfruit lover
                if not (pos_nat["swede"] < pos_smoothie["dragonfruit"]):
                    continue
                # Clue 7: Two houses between Lime and the Dane
                if abs(pos_smoothie["lime"] - pos_nat["dane"]) != 3:
                    continue

                # All constraints satisfied; build solution
                rows = []
                for i in houses:
                    rows.append([
                        str(i + 1),
                        name_at[i],
                        smoothie_at[i],
                        nat_at[i],
                    ])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "Nationality"],
                        "rows": rows
                    }
                }
                return solution

    return None

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))