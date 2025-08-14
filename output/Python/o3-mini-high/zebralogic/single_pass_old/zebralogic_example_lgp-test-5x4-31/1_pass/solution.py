#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations_list = ["cruise", "city", "camping", "beach", "mountain"]
    childs_list = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities_list = ["dane", "norwegian", "brit", "german", "swede"]
    
    # Pre-filter permutations with fixed positions:
    # House 1 (index 0): vacation is "cruise"
    valid_vacations = []
    for perm in itertools.permutations(vacations_list):
        if perm[0] == "cruise":
            valid_vacations.append(perm)
            
    # House 4 (index 3): child is "Meredith"
    valid_childs = []
    for perm in itertools.permutations(childs_list):
        if perm[3] == "Meredith":
            valid_childs.append(perm)
            
    # House 5 (index 4): nationality is "dane"
    valid_nationalities = []
    for perm in itertools.permutations(nationalities_list):
        if perm[4] == "dane":
            valid_nationalities.append(perm)
    
    solution = None

    for names in itertools.permutations(names_list):
        for vac in valid_vacations:
            # Constraint 13: The person who enjoys camping trips is not in the fifth house.
            if vac[4] == "camping":
                continue
            for ch in valid_childs:
                # Constraint 4: The child's name Bella is not in the second house.
                if ch[1] == "Bella":
                    continue
                for nat in valid_nationalities:
                    # Constraint 1: The Norwegian is Peter.
                    valid = True
                    for i in range(5):
                        if nat[i] == "norwegian" and names[i] != "Peter":
                            valid = False
                            break
                    if not valid:
                        continue
                        
                    # Constraint 2: The Swedish person's child is named Bella.
                    for i in range(5):
                        if nat[i] == "swede" and ch[i] != "Bella":
                            valid = False
                            break
                    if not valid:
                        continue
                        
                    # Constraint 5: Alice is the British person.
                    for i in range(5):
                        if names[i] == "Alice" and nat[i] != "brit":
                            valid = False
                            break
                    if not valid:
                        continue
                        
                    # Constraint 8: Eric is not in the fifth house.
                    if names[4] == "Eric":
                        continue
                        
                    # Constraint 11: Bob is the person who enjoys camping trips.
                    try:
                        idx_bob = names.index("Bob")
                        if vac[idx_bob] != "camping":
                            continue
                    except ValueError:
                        continue
                        
                    # Constraint 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
                    try:
                        idx_beach = vac.index("beach")
                    except ValueError:
                        continue
                    if idx_beach == 4 or ch[idx_beach + 1] != "Samantha":
                        continue
                        
                    # Constraint 9: The Swedish person is somewhere to the right of the Norwegian.
                    try:
                        idx_norwegian = nat.index("norwegian")
                        idx_swede = nat.index("swede")
                    except ValueError:
                        continue
                    if idx_swede <= idx_norwegian:
                        continue
                        
                    # Constraint 10: There is one house between the house with child Fred and the house that prefers city breaks.
                    try:
                        idx_fred = ch.index("Fred")
                        idx_city = vac.index("city")
                    except ValueError:
                        continue
                    if abs(idx_fred - idx_city) != 2:
                        continue
                        
                    # All constraints passed; we found a solution
                    solution = []
                    for i in range(5):
                        # House numbers are 1-indexed in output.
                        solution.append([str(i+1), names[i], vac[i], ch[i], nat[i]])
                    output = {
                        "solution": {
                            "header": ["House", "Name", "vacation", "child", "nationality"],
                            "rows": solution
                        }
                    }
                    print(json.dumps(output, indent=2))
                    return

if __name__ == "__main__":
    main()