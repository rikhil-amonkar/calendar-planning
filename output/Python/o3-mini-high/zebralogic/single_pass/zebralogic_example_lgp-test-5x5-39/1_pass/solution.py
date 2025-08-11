#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Fixed lists from the puzzle
    # There are five houses (index 0 = House 1, index 1 = House 2, ..., index 4 = House 5).
    # Names: Bob will be fixed in the fourth house (House 4, index 3) by deduction.
    names_all = ["Alice", "Eric", "Peter", "Arnold"]
    # The full set for all 5 houses is: one house gets Bob (fixed) and the other 4 are a permutation of names_all.
    
    # Mapping from name to occupation and hair (from clues):
    # Clue 3: Eric is the doctor.
    # Clue 15: Peter is the lawyer.
    # Clue 9 & 17: The person with gray hair is the teacher and Alice is that person.
    # Clue 13: Arnold has blonde hair and by elimination, the remaining hair for Eric is red.
    mapping_occ = {"Alice": "teacher", "Eric": "doctor", "Peter": "lawyer", "Arnold": "engineer", "Bob": "artist"}
    mapping_hair = {"Alice": "gray", "Eric": "red", "Peter": "black", "Arnold": "blonde", "Bob": "brown"}
    
    # Fixed month placements per puzzle:
    # Clue 2: House 1 (index 0) birthday is 'feb'
    # Clue 1: House 5 (index 4) birthday is 'mar'
    # Clue 6 & 12: The artist (in House 4, index 3) has brown hair and birthday is in 'jan'
    fixed_months = {0: "feb", 3: "jan", 4: "mar"}
    # The remaining months (for Houses 2 and 3 i.e. indices 1 and 2) are "april" and "sept" in some order.
    month_options = [
        ["feb", "april", "sept", "jan", "mar"],
        ["feb", "sept", "april", "jan", "mar"]
    ]
    
    # Mothers available: from puzzle list.
    mothers_all = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    # Clue 4: The person whose mother is Janelle lives in the third house (House 3, index 2).
    # When iterating mothers, we will fix index 2 to "Janelle".
    # Also Clue 10: Alice's mother is Kailyn.
    # Clue 14: The person whose mother is Holly has black hair (and by Clue 8 Peter has black hair).
    
    # Iterate over all assignments of names for houses (except House 4 which is fixed to Bob).
    # Houses: indices 0,1,2,4 will be assigned a permutation of ["Alice", "Eric", "Peter", "Arnold"].
    for perm_names in itertools.permutations(names_all):
        # Build full names list of length 5.
        # House indices:
        # 0: ? , 1: ? , 2: ? , 3: fixed as "Bob", 4: ?
        names = [None] * 5
        names[0] = perm_names[0]
        names[1] = perm_names[1]
        names[2] = perm_names[2]
        names[3] = "Bob"  # Fixed by deduction.
        names[4] = perm_names[3]
        
        # Determine occupations and hair from the names using our mappings.
        occ = [ mapping_occ[name] for name in names ]
        hair = [ mapping_hair[name] for name in names ]
        
        # Try all possible month assignments (only two possibilities for indices 1 and 2)
        for months in month_options:
            # Check fixed month positions are honored (they are built into month_options).
            # Find index of the house with month "sept"
            try:
                idx_sept = months.index("sept")
            except ValueError:
                continue

            # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
            try:
                idx_arnold = names.index("Arnold")
            except ValueError:
                continue
            if not (idx_arnold > idx_sept):
                continue

            # Clue 16: The person whose birthday is in September is somewhere to the left of the person whose mother's name is Kailyn.
            # Since Clue 10 says Alice's mother is Kailyn, this means the house with "sept" must be left of the house where Alice is.
            try:
                idx_alice = names.index("Alice")
            except ValueError:
                continue
            if not (idx_alice > idx_sept):
                continue

            # Now iterate over mothers assignment.
            # We need to fix House 3 mothers by assigning mothers to indices 0,1,3,4 from the set mothers_all minus {"Janelle"} 
            # and force index 2 to be "Janelle" (House 3 per clue 4).
            remaining_mothers = [m for m in mothers_all if m != "Janelle"]
            for perm_mothers in itertools.permutations(remaining_mothers, 4):
                mothers = [None] * 5
                mothers[0] = perm_mothers[0]
                mothers[1] = perm_mothers[1]
                mothers[2] = "Janelle"  # Fixed for third house
                mothers[3] = perm_mothers[2]
                mothers[4] = perm_mothers[3]
                
                valid = True
                # Clue 10: Alice's mother must be Kailyn.
                for i in range(5):
                    if names[i] == "Alice":
                        if mothers[i] != "Kailyn":
                            valid = False
                            break
                    # Clue 8 & 14: Peter is the person with black hair and his mother must be Holly.
                    if names[i] == "Peter":
                        if mothers[i] != "Holly":
                            valid = False
                            break
                if not valid:
                    continue
                
                # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person with black hair (Peter).
                try:
                    idx_peter = names.index("Peter")
                except ValueError:
                    continue
                for i in range(5):
                    if mothers[i] == "Penny" and i >= idx_peter:
                        valid = False
                        break
                if not valid:
                    continue
                
                # Clue 14 (reinforced): any house with mother Holly must be the one with black hair.
                for i in range(5):
                    if mothers[i] == "Holly" and hair[i] != "black":
                        valid = False
                        break
                if not valid:
                    continue
                
                # If all constraints are satisfied, we have found the solution.
                # Build the solution output.
                solution_rows = []
                for i in range(5):
                    # House numbers are 1-indexed.
                    row = [str(i+1), names[i], months[i], mothers[i], occ[i], hair[i]]
                    solution_rows.append(row)
                solution = {
                    "solution": {
                        "header": ["House", "Name", "birthday", "mother", "occupation", "hair"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution))
                sys.exit(0)
                
if __name__ == '__main__':
    main()