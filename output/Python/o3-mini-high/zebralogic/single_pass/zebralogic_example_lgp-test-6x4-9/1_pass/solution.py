#!/usr/bin/env python3
import itertools
import json

def valid_solution(names, phones, nats, colors):
    # Constraint 1: Carol is not in the third house (house number 3 -> index 2)
    if names[2] == "Carol":
        return False

    # Constraint 3: Carol is the person whose favorite color is green.
    # And if color is green then that house must be Carol.
    for i in range(6):
        if names[i] == "Carol" and colors[i] != "green":
            return False
        if colors[i] == "green" and names[i] != "Carol":
            return False

    # Constraint 4: Arnold is directly left of Alice.
    if "Arnold" in names and "Alice" in names:
        idx_arnold = names.index("Arnold")
        # Arnold cannot be in the last house because then no one is to his right.
        if idx_arnold == 5 or names[idx_arnold + 1] != "Alice":
            return False

    # Constraint 5: Alice is the German.
    for i in range(6):
        if names[i] == "Alice" and nats[i] != "german":
            return False

    # Constraint 6: The person who uses a OnePlus 9 is the person who loves purple.
    # This is bidirectional.
    for i in range(6):
        if phones[i] == "oneplus 9" and colors[i] != "purple":
            return False
        if colors[i] == "purple" and phones[i] != "oneplus 9":
            return False

    # Constraint 7: The person who uses a Huawei P50 is not in the third house (index 2).
    if phones[2] == "huawei p50":
        return False

    # Constraint 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
    if phones[4] != "samsung galaxy s21":
        return False

    # Constraint 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
    # Only check among houses where red and white can appear (they are assigned in the non‐fixed positions).
    red_index = None
    white_index = None
    for i in [0, 1, 2, 4]:
        if colors[i] == "red":
            red_index = i
        if colors[i] == "white":
            white_index = i
    if red_index is None or white_index is None or not (red_index < white_index):
        return False

    # Constraint 10: The person who uses a Samsung Galaxy S21 is Bob.
    if names[4] != "Bob":
        return False

    # Constraint 11: The Dane is the person who loves yellow.
    for i in range(6):
        if nats[i] == "dane" and colors[i] != "yellow":
            return False

    # Constraint 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    # (House 5 index 4 and Peter is house 6 index 5; already fixed so it's automatically satisfied.)
    
    # Constraint 13: The person who loves blue is Peter.
    if colors[5] != "blue" or names[5] != "Peter":
        return False

    # Constraint 14: Peter is the British person.
    if nats[5] != "brit":
        return False

    # Constraint 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    # (House 5 index 4 and House 6 index 5; already fixed.)
    
    # Constraint 16: The Norwegian is the person who loves purple.
    # So if a house's nationality is norwegian, its color must be purple and phone must be oneplus 9.
    for i in range(6):
        if nats[i] == "norwegian":
            if colors[i] != "purple" or phones[i] != "oneplus 9":
                return False
        # Additionally, if a house has color purple, then nationality must be norwegian.
        if colors[i] == "purple" and nats[i] != "norwegian":
            return False

    # Constraint 17: The person who uses a Xiaomi Mi 11 is the Chinese.
    for i in range(6):
        if phones[i] == "xiaomi mi 11" and nats[i] != "chinese":
            return False
        if nats[i] == "chinese" and phones[i] != "xiaomi mi 11":
            return False

    return True

def main():
    # There are 6 houses with indices 0..5 corresponding to house numbers 1..6.
    # Fixed assignments given the clues:
    # Names: House 5 (index 4) is Bob, House 6 (index 5) is Peter.
    fixed_names = {4: "Bob", 5: "Peter"}
    # Phones: House 5 (index 4) is samsung galaxy s21, House 6 (index 5) is iphone 13.
    fixed_phones = {4: "samsung galaxy s21", 5: "iphone 13"}
    # Nationalities: House 4 (index 3) is dane (and by clue 11 must love yellow), House 6 (index 5) is brit.
    fixed_nats = {3: "dane", 5: "brit"}
    # Colors: House 4 (index 3) must be yellow (for the Dane) and House 6 (index 5) is blue (for Peter).
    fixed_colors = {3: "yellow", 5: "blue"}
    
    # Remaining possible values:
    available_names = ["Carol", "Alice", "Arnold", "Eric"]  # for indices 0,1,2,3 (index3 gets name even though nat/color fixed)
    available_phones = ["google pixel 6", "huawei p50", "oneplus 9", "xiaomi mi 11"]  # for indices 0,1,2,3
    available_nats = ["swede", "chinese", "norwegian", "german"]  # for indices 0,1,2,4 (because indices 3 and 5 are fixed)
    available_colors = ["red", "green", "white", "purple"]  # for indices 0,1,2,4 (indices 3 and 5 fixed)

    solution_found = False
    final_solution = {}
    # Iterate over permutations for names (to fill indices 0,1,2,3)
    for name_perm in itertools.permutations(available_names):
        names = [None] * 6
        # assign permutation to indices 0,1,2,3
        for i, val in enumerate(name_perm):
            names[i] = val
        # set fixed names for houses 5 and 6
        for idx, val in fixed_names.items():
            names[idx] = val

        # Iterate over permutations for nationalities for indices 0,1,2,4
        for nat_perm in itertools.permutations(available_nats):
            nats = [None] * 6
            # assign according to predetermined indices: assign nat[0], nat[1], nat[2] and nat[4]
            nats[0] = nat_perm[0]
            nats[1] = nat_perm[1]
            nats[2] = nat_perm[2]
            nats[4] = nat_perm[3]
            # set fixed nationalities at index 3 and 5
            for idx, val in fixed_nats.items():
                nats[idx] = val

            # Iterate over permutations for phones for indices 0,1,2,3
            for phone_perm in itertools.permutations(available_phones):
                phones = [None] * 6
                for i, val in enumerate(phone_perm):
                    phones[i] = val
                for idx, val in fixed_phones.items():
                    phones[idx] = val

                # Iterate over permutations for colors for indices 0,1,2,4
                for color_perm in itertools.permutations(available_colors):
                    colors = [None] * 6
                    colors[0] = color_perm[0]
                    colors[1] = color_perm[1]
                    colors[2] = color_perm[2]
                    colors[4] = color_perm[3]
                    for idx, val in fixed_colors.items():
                        colors[idx] = val

                    # Now check all constraints
                    if valid_solution(names, phones, nats, colors):
                        # We found a solution, record it.
                        final_solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                                "rows": []
                            }
                        }
                        for i in range(6):
                            row = [str(i+1), names[i], phones[i], nats[i], colors[i]]
                            final_solution["solution"]["rows"].append(row)
                        solution_found = True
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break

    # Output the solution as JSON formatted output.
    print(json.dumps(final_solution, indent=2))

if __name__ == "__main__":
    main()