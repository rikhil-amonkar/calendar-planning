import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    Mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    Heights = ["average", "very short", "short", "very tall", "tall"]

    # Helper to create reverse lookup: value -> position (0-based)
    def pos_map(assign_list):
        return {assign_list[i]: i for i in range(5)}

    solution = None

    for names_perm in permutations(Names):
        # Clue 4: Peter is not in the second house.
        if names_perm[1] == "Peter":
            continue
        # Clue 8: Eric is not in the fifth house.
        if names_perm[4] == "Eric":
            continue

        pos_name = pos_map(names_perm)

        # Iterate mothers with constraints 1,3,10 applied
        for mothers_perm in permutations(Mothers):
            pos_mother = pos_map(mothers_perm)

            # Clue 1: Alice is the person whose mother's name is Aniya.
            if pos_name["Alice"] != pos_mother["Aniya"]:
                continue
            # Clue 3: The person whose mother's name is Janelle is Bob.
            if pos_name["Bob"] != pos_mother["Janelle"]:
                continue
            # Clue 10: Eric is the person whose mother's name is Kailyn.
            if pos_name["Eric"] != pos_mother["Kailyn"]:
                continue
            # Clue 9 with Clue 6 (to be enforced later) implies:
            # Arnold (very tall) is somewhere to the right of the person whose mother's name is Holly.
            if pos_name["Arnold"] <= pos_mother["Holly"]:
                continue

            for heights_perm in permutations(Heights):
                pos_height = pos_map(heights_perm)

                # Clue 11: The person who is very short is in the fifth house.
                if heights_perm[4] != "very short":
                    continue
                # Clue 6: The person who is very tall is Arnold.
                if pos_height["very tall"] != pos_name["Arnold"]:
                    continue
                # Clue 5: The person who is short is directly left of Arnold.
                if pos_height["short"] + 1 != pos_name["Arnold"]:
                    continue
                # Clue 7: Bob is directly left of the person who has an average height.
                if pos_name["Bob"] + 1 != pos_height["average"]:
                    continue
                # Clue 2: The person who has an average height is somewhere to the left of the person whose mother's name is Penny.
                if not (pos_height["average"] < pos_mother["Penny"]):
                    continue
                # Clue 9: The person who is very tall is somewhere to the right of the person whose mother's name is Holly.
                if not (pos_height["very tall"] > pos_mother["Holly"]):
                    continue

                # Found a valid solution
                solution = {
                    "header": ["House", "Name", "Mother", "Height"],
                    "rows": []
                }
                for i in range(5):
                    solution["rows"].append([
                        str(houses[i]),
                        names_perm[i],
                        mothers_perm[i],
                        heights_perm[i],
                    ])
                return solution

    return None

def main():
    result = solve_puzzle()
    output = {"solution": result if result else {}}
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()