import itertools
import json

def main():
    # There are 6 houses: positions 1 through 6.
    # Fixed phone assignments based on clues:
    # Clue 2: House 1 has "huawei p50"
    # Clue 8: House 3 has "xiaomi mi 11"
    # Clue 3: House 6 has "oneplus 9"
    # Clue 7: The person with "huawei p50" is Eric => House 1 must be Eric.
    # Clue 10: The person with "oneplus 9" is Arnold => House 6 must be Arnold.
    fixed_phones = {
        1: "huawei p50",
        3: "xiaomi mi 11",
        6: "oneplus 9"
    }
    
    # For house 2, available phone models (from the set) are:
    # Remaining phone models: "iphone 13", "samsung galaxy s21", "google pixel 6"
    # Clue 5: iPhone 13 is not in house 2.
    # Clue 4: Google Pixel 6 is not in house 2.
    # Thus, House 2 must have "samsung galaxy s21".
    fixed_phones[2] = "samsung galaxy s21"
    
    # Houses 4 and 5 will then get the remaining two phone models:
    remaining_phones = ["iphone 13", "google pixel 6"]
    # They can be in either order.
    phone_options_45 = list(itertools.permutations(remaining_phones))
    
    # Fixed names based on clues:
    # Clue 7: The person with Huawei P50 is Eric (House 1).
    # Clue 10: Arnold uses OnePlus 9 (House 6).
    fixed_names = {1: "Eric", 6: "Arnold"}
    
    # Remaining names for houses 2, 3, 4, 5:
    # The full set of names:
    all_names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    # Remove Arnold and Eric
    remaining_names = [name for name in ["Alice", "Bob", "Carol", "Peter"]]
    
    solution_found = None
    
    # Permute the assignments of remaining names to houses 2, 3, 4, and 5.
    for perm in itertools.permutations(remaining_names):
        names = fixed_names.copy()
        names[2] = perm[0]
        names[3] = perm[1]
        names[4] = perm[2]
        names[5] = perm[3]
        
        # Now iterate through the possible phone assignments for houses 4 and 5.
        for option in phone_options_45:
            phones = fixed_phones.copy()
            phones[4] = option[0]
            phones[5] = option[1]
            
            # Constraint: The person who uses an iPhone 13 is Alice (Clue 1).
            # Thus, if a house's phone is "iphone 13", that house's name must be "Alice".
            valid = True
            for house in range(1, 7):
                if phones[house] == "iphone 13" and names[house] != "Alice":
                    valid = False
                    break
            if not valid:
                continue
            
            # Constraint: Alice is somewhere to the left (i.e., lower house number) of Carol (Clue 9).
            house_alice = next((num for num, n in names.items() if n == "Alice"), None)
            house_carol = next((num for num, n in names.items() if n == "Carol"), None)
            if house_alice is None or house_carol is None or house_alice >= house_carol:
                continue

            # Constraint: There is exactly one house between Bob and Carol (Clue 6).
            house_bob = next((num for num, n in names.items() if n == "Bob"), None)
            if house_bob is None or abs(house_bob - house_carol) != 2:
                continue

            # All other clues are inherently satisfied by the fixed assignments.
            solution_found = (names.copy(), phones.copy())
            break
        if solution_found:
            break

    if solution_found:
        sol_names, sol_phones = solution_found
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": []
            }
        }
        # Ensure houses are output in numerical order 1-6.
        for house in range(1, 7):
            result["solution"]["rows"].append([str(house), sol_names[house], sol_phones[house]])
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == "__main__":
    main()