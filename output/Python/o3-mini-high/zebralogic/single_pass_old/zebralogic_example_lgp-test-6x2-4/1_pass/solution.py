#!/usr/bin/env python3
import itertools
import json

def main():
    # There are 6 houses (index 0 = House 1, index 5 = House 6).
    # Names: Alice, Arnold, Carol, Peter, Bob, Eric
    # Phones: huawei p50, iphone 13, xiaomi mi 11, oneplus 9, samsung galaxy s21, google pixel 6

    # Fixed information from clues:
    # Clue 2: House 1 uses "huawei p50"
    # Clue 7: The person who uses "huawei p50" is Eric, so House 1 must be Eric.
    # Clue 8: House 3 uses "xiaomi mi 11"
    # Clue 3: House 6 uses "oneplus 9"
    # Clue 10: The person who uses "oneplus 9" is Arnold, so House 6 must be Arnold.
    # Clues 4 & 5: "google pixel 6" and "iphone 13" cannot be in House 2.
    # Clue 1: The person who uses "iphone 13" is Alice.
    # Clue 9: Alice is somewhere to the left of Carol.
    # Clue 6: There is one house between Bob and Carol.

    # We'll assign phone models and names to houses 1..6 (indices 0 to 5)
    # Fixed phone assignments:
    #   House 1 (index 0): "huawei p50"
    #   House 3 (index 2): "xiaomi mi 11"
    #   House 6 (index 5): "oneplus 9"
    # The remaining three phones are: "iphone 13", "samsung galaxy s21", "google pixel 6"
    # House 2 (index 1) cannot have "iphone 13" nor "google pixel 6", so it must be "samsung galaxy s21".
    # That leaves Houses 4 and 5 (indices 3 and 4) to assign "iphone 13" and "google pixel 6" (in one order).
    
    fixed_phones = [None] * 6
    fixed_phones[0] = "huawei p50"         # House 1
    fixed_phones[1] = "samsung galaxy s21"   # House 2 is forced
    fixed_phones[2] = "xiaomi mi 11"         # House 3
    fixed_phones[5] = "oneplus 9"            # House 6
    
    # The two possibilities for houses 4 and 5:
    phone_options = [
        ["iphone 13", "google pixel 6"],
        ["google pixel 6", "iphone 13"]
    ]
    
    # Fixed name assignments using clues:
    # House 1 (index 0) must be Eric (clues 2 & 7) and House 6 (index 5) must be Arnold (clues 3 & 10).
    fixed_names = [None] * 6
    fixed_names[0] = "Eric"
    fixed_names[5] = "Arnold"
    
    # The remaining names to assign to Houses 2, 3, 4, and 5 are:
    remaining_names = ["Alice", "Carol", "Peter", "Bob"]
    
    solution = None
    
    # Iterate over the two possible assignments for houses 4 and 5
    for option in phone_options:
        phones = fixed_phones[:]  # make a copy
        phones[3] = option[0]      # House 4
        phones[4] = option[1]      # House 5
        
        # Additional phone constraints (Clues 4 and 5):
        # "google pixel 6" and "iphone 13" must not be in House 2 (index 1)
        if phones[1] in ["iphone 13", "google pixel 6"]:
            continue
        
        # Now iterate over all permutations for the remaining names in houses 2-5 (indices 1,2,3,4)
        for perm in itertools.permutations(remaining_names):
            names = fixed_names[:]  # start with fixed names
            names[1] = perm[0]  # House 2
            names[2] = perm[1]  # House 3
            names[3] = perm[2]  # House 4
            names[4] = perm[3]  # House 5
            
            valid = True
            
            # Clue 1: The person who uses "iphone 13" is Alice.
            for i in range(6):
                if phones[i] == "iphone 13" and names[i] != "Alice":
                    valid = False
                    break
            if not valid:
                continue
            
            # Clue 9: Alice is somewhere to the left of Carol.
            if names.index("Alice") >= names.index("Carol"):
                continue
            
            # Clue 6: There is one house between Bob and Carol.
            if abs(names.index("Bob") - names.index("Carol")) != 2:
                continue
            
            # If we reached here, all constraints are satisfied.
            solution = {
                "houses": list(range(1, 7)),
                "names": names,
                "phones": phones
            }
            break
        if solution:
            break

    # Build the output dictionary in the required JSON format.
    if solution:
        output = {
            "solution": {
                "header": ["House", "Name", "phone"],
                "rows": []
            }
        }
        for i in range(6):
            row = [str(i + 1), solution["names"][i], solution["phones"][i]]
            output["solution"]["rows"].append(row)
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()