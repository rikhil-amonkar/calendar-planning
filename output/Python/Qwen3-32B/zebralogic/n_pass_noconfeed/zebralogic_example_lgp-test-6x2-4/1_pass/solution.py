import itertools
import json

def solve_puzzle():
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]
    
    # Fixed positions
    fixed_names = ["Eric", None, None, None, None, "Arnold"]
    fixed_phones = ["huawei p50", "samsung galaxy s21", "xiaomi mi 11", None, None, "oneplus 9"]
    
    remaining_names = ["Alice", "Carol", "Peter", "Bob"]
    remaining_phones = ["iphone 13", "google pixel 6"]
    
    for name_perm in itertools.permutations(remaining_names):
        current_names = fixed_names.copy()
        current_names[1], current_names[2], current_names[3], current_names[4] = name_perm
        
        for phone_perm in itertools.permutations(remaining_phones):
            current_phones = fixed_phones.copy()
            current_phones[3], current_phones[4] = phone_perm
            
            # Check iPhone 13 is with Alice
            iphone13_index = current_phones.index("iphone 13")
            if current_names[iphone13_index] != "Alice":
                continue
            
            # Check Bob and Carol have one house between them
            bob_index = current_names.index("Bob")
            carol_index = current_names.index("Carol")
            if abs(bob_index - carol_index) != 2:
                continue
            
            # Check Alice is left of Carol
            alice_index = current_names.index("Alice")
            if alice_index >= carol_index:
                continue
            
            # Construct solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "PhoneModel"],
                    "rows": []
                }
            }
            for i in range(6):
                house = str(i + 1)
                solution["solution"]["rows"].append([house, current_names[i], current_phones[i]])
            
            print(json.dumps(solution, indent=2))
            return

solve_puzzle()