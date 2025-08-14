#!/usr/bin/env python3
import json
import itertools

def main():
    # Define lists of possible attributes
    names_list = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights_list = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones_list = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Fixed positions based on clues:
    # Clue 9: The person who is super tall is in the first house.
    # Clue 12: The person who is short is in the sixth house.
    fixed_height_first = "super tall"
    fixed_height_last = "short"
    # For the remaining houses (house 2-5, indices 1,2,3,4), the heights available are the remaining four.
    # However, clues 3 forces the person who is very short to be to the right of the google pixel 6 (see below)
    # and by Clue 5 (one house between google pixel 6 and short) and Clue 12 (short in house6),
    # this forces the house immediately left of the sixth house to be the one using OnePlus 9 (clue 7)
    # and in our height assignments we will force house index 4 (i.e. house5) to be "very short" if possible.
    # We choose to assign the flexible heights as follows:
    #   House 1 (index 0): fixed to "super tall"
    #   Houses 2,3,4 (indices 1,2,3): will be assigned a permutation of {"tall", "very tall", "average"}
    #   House 5 (index 4): forced to "very short" (to meet clue 3 with google pixel6, see below)
    #   House 6 (index 5): fixed to "short"
    # Clue 8 and 4 require: The person who is tall is Arnold and the person who is very tall is Carol.
    
    # For phones, fixed positions:
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    #   With short in house6 (index 5), Google Pixel 6 must be in house4 (index 3).
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    #   Thus, OnePlus 9 must be in house5 (index 4).
    fixed_phone_house3 = "google pixel 6"  # index 3 (4th house)
    fixed_phone_house4 = "oneplus 9"         # index 4 (5th house)

    # For heights: fixed houses: index0 and index5 are set.
    # And we force index4 (5th house) to be "very short" to ensure clue 3 holds.
    # The remaining houses where heights are free: indices 1,2,3.
    flexible_heights = ["tall", "very tall", "average"]
    
    # For phones: free positions are houses at indices: 0, 1, 2, and 5.
    free_phones = ["samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    solution = None

    for names_perm in itertools.permutations(names_list):
        # Clue 11: The person who uses Google Pixel 6 is somewhere to the right of Eric.
        # Google Pixel 6 is fixed in house 4 (index 3), so Eric must be in a house with index < 3.
        if names_perm.index("Eric") >= 3:
            continue

        # Clue 1: Bob is directly left of the person who is tall.
        idx_bob = names_perm.index("Bob")
        if idx_bob == 5:
            continue
        # The house immediately right of Bob must be occupied by Arnold (since clue 8 says "the person who is tall is Arnold")
        if names_perm[idx_bob + 1] != "Arnold":
            continue

        # Clue 4 & 10 implications: Carol must be very tall and use Xiaomi Mi 11.
        # Carol cannot be in a house with a fixed height that is not "very tall".
        # House 1 (index 0) is "super tall", house 5 (index 4) will be "very short", house 6 (index 5) is "short",
        # and house 4 (index 3) is flexible but will be assigned from flexible_heights.
        # Also, note: House with index 3 is fixed phone "google pixel 6", so Carol cannot be there (she must have Xiaomi Mi 11).
        # Thus, Carol must be in one of houses with indices 1 or 2.
        if names_perm.index("Carol") not in [1, 2]:
            continue

        # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
        # (Will check once phones are assigned)

        # Now assign heights for flexible houses.
        for heights_perm in itertools.permutations(flexible_heights):
            # Build full heights list for houses indices 0 to 5.
            # House0: fixed "super tall"
            # Houses 1,2,3: from heights_perm (in order)
            # House4: forced "very short"
            # House5: fixed "short"
            full_heights = [
                fixed_height_first,    # house 1
                heights_perm[0],       # house 2
                heights_perm[1],       # house 3
                heights_perm[2],       # house 4
                "very short",          # house 5
                fixed_height_last      # house 6
            ]
            # Clue 8: The person who is tall is Arnold.
            if "tall" not in full_heights:
                continue
            idx_tall = full_heights.index("tall")
            if names_perm[idx_tall] != "Arnold":
                continue

            # Clue 4: Carol is the person who is very tall.
            if "very tall" not in full_heights:
                continue
            idx_very_tall = full_heights.index("very tall")
            if names_perm[idx_very_tall] != "Carol":
                continue

            # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
            # We will enforce this later when phones are assigned, but our fixed assignment will suffice:
            # "Google Pixel 6" is in house 4 (index 3) and "very short" is in house 5 (index 4) -> 4 > 3.
            if full_heights.index("very short") <= 3:
                continue

            # Now assign phones for the free positions
            for free_phone_perm in itertools.permutations(free_phones):
                full_phones = [None] * 6
                # free positions: indices 0, 1, 2, and 5.
                full_phones[0] = free_phone_perm[0]
                full_phones[1] = free_phone_perm[1]
                full_phones[2] = free_phone_perm[2]
                # Fixed assignments:
                full_phones[3] = fixed_phone_house3  # house 4
                full_phones[4] = fixed_phone_house4  # house 5
                full_phones[5] = free_phone_perm[3]

                # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
                if full_phones[0] == "samsung galaxy s21":
                    continue

                # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
                # That means: the house occupied by Carol must have phone "xiaomi mi 11".
                idx_carol = names_perm.index("Carol")
                if full_phones[idx_carol] != "xiaomi mi 11":
                    continue
                # Also, if any house has phone "xiaomi mi 11", its occupant must be Carol.
                valid_xiaomi = True
                for i in range(6):
                    if full_phones[i] == "xiaomi mi 11" and names_perm[i] != "Carol":
                        valid_xiaomi = False
                        break
                if not valid_xiaomi:
                    continue

                # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
                try:
                    idx_iphone = full_phones.index("iphone 13")
                except ValueError:
                    continue
                if names_perm.index("Peter") >= idx_iphone:
                    continue

                # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
                # Check: find the index of "oneplus 9" in full_phones and ensure the next house (if exists) has height "short".
                try:
                    idx_oneplus = full_phones.index("oneplus 9")
                except ValueError:
                    continue
                if idx_oneplus == 5:
                    continue
                if full_heights[idx_oneplus + 1] != "short":
                    continue

                # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
                # Google Pixel 6 is fixed in house 4 (index 3). Eric must be in a house with index less than 3.
                if names_perm.index("Eric") >= 3:
                    continue

                # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
                # Google Pixel 6 is in house 4 (index 3) and "short" is in house 6 (index 5); check the distance.
                if abs(full_phones.index("google pixel 6") - full_heights.index("short")) != 2:
                    continue

                # All constraints satisfied. Save the solution.
                solution = {
                    "names": names_perm,
                    "heights": full_heights,
                    "phones": full_phones
                }
                break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is None:
        result = {"solution": {"header": ["House", "Name", "Height", "Phone"], "rows": []}}
    else:
        # Build the table in order of houses 1 to 6.
        rows = []
        # Houses are numbered 1 to 6 (indices 0 to 5)
        for i in range(6):
            row = [str(i+1), solution["names"][i], solution["heights"][i], solution["phones"][i]]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Phone"],
                "rows": rows
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()