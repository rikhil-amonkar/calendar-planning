#!/usr/bin/env python3
import itertools
import json

def main():
    # Define attributes
    names_all = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies_all = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities_all = ["german", "swede", "norwegian", "dane", "brit"]

    solution_found = None

    # The houses are indexed 0 to 4 corresponding to houses 1 to 5.
    for names in itertools.permutations(names_all):
        # Constraint 10: Alice is in the third house (index 2)
        if names[2] != "Alice":
            continue
        # Constraint 3: Peter is not in the first house (index 0)
        if names[0] == "Peter":
            continue

        for smoothies in itertools.permutations(smoothies_all):
            # Constraint 2: The Dragonfruit smoothie lover is in the second house (index 1)
            if smoothies[1] != "dragonfruit":
                continue
            # Constraint 11: The Watermelon smoothie lover is in the third house (index 2)
            if smoothies[2] != "watermelon":
                continue
            # Constraint 5: The Desert smoothie lover is not in the fifth house (index 4)
            if smoothies[4] == "desert":
                continue

            for nat in itertools.permutations(nationalities_all):
                # Constraint 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
                # Since Dragonfruit is in the second house (index 1), the Swedish (swede) must be in house 1 (index 0).
                if nat[0] != "swede":
                    continue
                # Constraint 9: Alice is the Norwegian.
                # Alice is in house 3 (index 2)
                if nat[2] != "norwegian":
                    continue

                # Constraint 8: Bob is the Dane.
                try:
                    bob_index = names.index("Bob")
                except ValueError:
                    continue
                if nat[bob_index] != "dane":
                    continue

                # Constraint 4: The Dane and the British person are next to each other.
                try:
                    brit_index = nat.index("brit")
                except ValueError:
                    continue
                if abs(bob_index - brit_index) != 1:
                    continue

                # Constraint 7: There are two houses between the person who drinks Lime smoothies and the Dane.
                try:
                    lime_index = smoothies.index("lime")
                except ValueError:
                    continue
                if abs(lime_index - bob_index) != 3:
                    continue

                # Constraint 1: The Dragonfruit smoothie lover is somewhere to the left of Eric.
                try:
                    eric_index = names.index("Eric")
                except ValueError:
                    continue
                # Dragonfruit smoothie is in the second house (index 1)
                if eric_index <= 1:
                    continue

                # If all constraints are satisfied, we have a solution.
                solution_found = {
                    "names": names,
                    "smoothies": smoothies,
                    "nationalities": nat
                }
                break
            if solution_found:
                break
        if solution_found:
            break

    if solution_found:
        # Build the output structure as specified.
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": []
            }
        }
        for i in range(5):
            row = [
                str(i+1),
                solution_found["names"][i],
                solution_found["smoothies"][i],
                solution_found["nationalities"][i]
            ]
            result["solution"]["rows"].append(row)
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()