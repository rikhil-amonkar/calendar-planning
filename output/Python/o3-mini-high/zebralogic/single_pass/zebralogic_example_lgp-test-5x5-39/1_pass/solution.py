#!/usr/bin/env python3
import json
import itertools

def solve_puzzle():
    # Houses are numbered 1 to 5 (indices 0..4)
    # Fixed domains for each category:
    # Names: ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    # Birthday months: ["mar", "april", "sept", "feb", "jan"]
    # Mothers: ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    # Occupations: ["engineer", "doctor", "lawyer", "artist", "teacher"]
    # Hair colors: ["red", "blonde", "black", "gray", "brown"]
    #
    # From the clues, we deduce many fixed relationships:
    #  - Clue 1: House5's birthday = "mar"
    #  - Clue 2: House1's birthday = "feb"
    #  - Clue 6: The person in House4 is the artist.
    #  - Clue 12: The brown-haired person has birthday "jan".
    #  - Clue 4: House3's mother = "Janelle"
    #  - Clue 10: Alice's mother = "Kailyn"
    #  - Clue 17: Alice has gray hair.
    #  - Clue 8: Peter has black hair.
    #  - Clue 14: The person whose mother is Holly has black hair.
    #  - Clue 3: The doctor is Eric.
    #  - Clue 15: The lawyer is Peter.
    #  - Clue 9: The person with gray hair is the teacher.
    #  - Clue 13: Arnold has blonde hair.
    #  - From clues 5 and 6: The artist has brown hair. Combined with clue 12, the artist’s birthday is "jan".
    #  - It then follows from the occupations that the remaining person must be the engineer.
    #
    # Also from deduction:
    #  - Since the artist is in House4 and the artist must have brown hair, and the only possible candidate (by elimination using other hair clues)
    #    is Bob, we conclude: House4 must be Bob.
    #  - Similarly, because Alice must have gray hair and be teacher, she can’t be in Houses that are already fixed by other clues.
    #    The only possibility is House5, so House5 = Alice.
    #  - The remaining names for Houses 1-3 (indices 0,1,2) are then {"Eric", "Peter", "Arnold"}.
    #
    # We also have two birthdays left for Houses 2 and 3 (indices 1 and 2) from:
    #   {"april", "sept"} (since House1 = "feb", House4 = "jan", House5 = "mar").
    #
    # Occupation assignment via names is fixed:
    #   Eric -> doctor   (Clue 3)
    #   Peter -> lawyer   (Clue 15) and must have black hair (Clues 8 and 14)
    #   Bob -> artist     (Clues 5,6,12) and his birthday = "jan" and hair = "brown"
    #   Alice -> teacher  (Clues 9,17) and hair = "gray"
    #   The remaining (Arnold) -> engineer, and Arnold must have blonde hair (Clue 13)
    #
    # Hair color assignment via names becomes:
    #   Alice: gray
    #   Eric: (the only remaining allowed is red, because the others are fixed below)
    #   Bob: brown
    #   Peter: black
    #   Arnold: blonde
    #
    # Mothers assignment must satisfy:
    #   - House3 (index2) mother = "Janelle" (Clue 4)
    #   - The person named Alice has mother "Kailyn" (Clue 10)
    #   - The person named Peter has mother "Holly" (from Clues 8 and 14)
    #   - The remaining two mothers will be "Penny" and "Aniya".
    #   - Clue 7: The house with mother "Penny" is somewhere to the left of the house with the person having black hair (Peter).
    #
    # Ordering constraints on birthdays:
    #   - Clue 11: The person with birthday "sept" is to the left of the person named Arnold.
    #   - Clue 16: The house with birthday "sept" is to the left of the house with the person whose mother is "Kailyn" (Alice).
    
    # Fixed mappings based on the above deductions:
    occupation_for = {
        "Alice": "teacher",
        "Eric": "doctor",
        "Bob": "artist",
        "Peter": "lawyer",
        "Arnold": "engineer"
    }
    hair_for = {
        "Alice": "gray",
        "Eric": "red",      # only remaining option after assigning black, brown, gray, blonde
        "Bob": "brown",
        "Peter": "black",
        "Arnold": "blonde"
    }
    
    # Fixed birthday placements (by house index):
    # House1 (index 0): "feb"
    # House4 (index 3): "jan"   (because the artist with brown hair must have jan)
    # House5 (index 4): "mar"
    fixed_birthdays = {0: "feb", 3: "jan", 4: "mar"}
    # The remaining two houses (indices 1 and 2) get {"sept", "april"} in some order.
    remaining_birthdays = ["sept", "april"]
    
    # We'll iterate over assignments for:
    #   - Names for houses 0,1,2 from permutation of ["Eric", "Peter", "Arnold"].
    #   - Mothers: full permutation for 5 houses from ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"],
    #       with fixed constraints:
    #         house index2 must be "Janelle"
    #         house with name "Alice" (which will be fixed in house index4) must get "Kailyn"
    #         house with name "Peter" must get "Holly"
    #   - Birthdays for houses 1 and 2 from the two possibilities.
    #
    # Fixed names for houses:
    #   House index 3: "Bob"
    #   House index 4: "Alice"
    
    solution = None
    
    all_mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    
    # Iterate over possible names for houses 0,1,2 (3! possibilities)
    for names_perm in itertools.permutations(["Eric", "Peter", "Arnold"], 3):
        # Build full names list for 5 houses: indices 0-4.
        names = [None] * 5
        names[0], names[1], names[2] = names_perm
        names[3] = "Bob"    # House 4
        names[4] = "Alice"  # House 5
        
        # Enforce an ordering constraint from clue 7:
        # Clue 7: The house whose mother is "Penny" must be to the left of the black hair person.
        # We don't know mothers yet, but we know the black hair person is Peter.
        # So Peter cannot be in the first house because then no house is to its left to hold "Penny".
        # So if Peter is in index 0, skip.
        if names.index("Peter") == 0:
            continue
        
        # Iterate over the two ways to assign birthdays to houses indices 1 and 2.
        for bd_perm in itertools.permutations(remaining_birthdays, 2):
            birthdays = [None] * 5
            birthdays[0] = fixed_birthdays[0]  # "feb"
            birthdays[3] = fixed_birthdays[3]  # "jan"
            birthdays[4] = fixed_birthdays[4]  # "mar"
            birthdays[1] = bd_perm[0]
            birthdays[2] = bd_perm[1]
            
            # Enforce clue 11 and 16 conditions:
            # Clue 11: The person with birthday "sept" must be to the left of the person named "Arnold".
            try:
                idx_sept = birthdays.index("sept")
            except ValueError:
                continue
            idx_arnold = names.index("Arnold")
            if idx_sept >= idx_arnold:
                continue
            # Clue 16: The house with birthday "sept" must be to the left of the house with mother "Kailyn"
            # Since we know that the person named "Alice" (who must have mother "Kailyn") is in house index 4,
            # we need to ensure that idx_sept < 4.
            if idx_sept >= 4:
                continue
            
            # Now iterate over permutations of mothers assignments (5! possibilities).
            for moms_perm in itertools.permutations(all_mothers):
                mothers = list(moms_perm)
                # Enforce fixed mothers from clues:
                # Clue 4: House3 (index 2) mother's must be "Janelle"
                if mothers[2] != "Janelle":
                    continue
                # Clue 10: The house with "Alice" must have mother "Kailyn".
                idx_alice = names.index("Alice")
                if mothers[idx_alice] != "Kailyn":
                    continue
                # Clue 14: The person whose mother is "Holly" has black hair.
                # And we know black hair person must be Peter.
                idx_peter = names.index("Peter")
                if mothers[idx_peter] != "Holly":
                    continue
                # Clue 7: The house with mother "Penny" must be to the left of the house with the black hair person (Peter).
                try:
                    idx_penny = mothers.index("Penny")
                except ValueError:
                    continue
                if idx_penny >= idx_peter:
                    continue
                
                # Construct the candidate solution as a list of houses (dictionaries)
                houses = []
                for i in range(5):
                    house_number = str(i+1)
                    name = names[i]
                    birthday = birthdays[i]
                    mother = mothers[i]
                    occupation = occupation_for[name]  # determined by name
                    hair = hair_for[name]             # determined by name
                    
                    house = {
                        "House": house_number,
                        "Name": name,
                        "Birthday": birthday,
                        "Mother": mother,
                        "Occupation": occupation,
                        "HairColor": hair
                    }
                    houses.append(house)
                
                # Additional check: Clue 12: The person who has brown hair has birthday "jan".
                # The person with brown hair is Bob; Bob should be in house 4 (index 3).
                if not (names[3] == "Bob" and birthdays[3] == "jan"):
                    continue
                # Clue 9 is automatically satisfied via fixed mapping (Alice:gray and teacher)
                # Clue 13: Arnold is blonde (ensured via mapping)
                # Clue 3,15,17 already fixed by mapping.
                # Clue 5: Artist is person with brown hair (Bob, already holds brown hair).
                # Clue 11 and 16 already checked.
                
                # If all constraints satisfied, we have found a valid solution.
                solution = houses
                return solution
    return None

def main():
    sol = solve_puzzle()
    if sol is None:
        output = {"solution": {"header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"], "rows": []}}
    else:
        # Arrange solution in house order (already in order 1..5)
        rows = []
        for house in sol:
            rows.append([house["House"], house["Name"], house["Birthday"], house["Mother"], house["Occupation"], house["HairColor"]])
        output = {"solution": {"header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"], "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()