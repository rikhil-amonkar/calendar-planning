#!/usr/bin/env python3
import json
import itertools

def solve():
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]
    
    solution = None
    
    # Iterate over all permutations of names and phones
    for people in itertools.permutations(names):
        # Constraint: House 1 must be Eric; House 6 must be Arnold.
        if people[0] != "Eric" or people[5] != "Arnold":
            continue
            
        for phone in itertools.permutations(phones):
            # Fixed phone assignments based on clues:
            # Clue 2: Huawei P50 is in the first house.
            if phone[0] != "huawei p50":
                continue
            # Clue 8: Xiaomi Mi 11 is in the third house.
            if phone[2] != "xiaomi mi 11":
                continue
            # Clue 3: OnePlus 9 is in the sixth house.
            if phone[5] != "oneplus 9":
                continue
            # Clues 4 and 5: iPhone 13 and Google Pixel 6 are not in the second house.
            # Given available models, house 2 must then be assigned samsung galaxy s21.
            if phone[1] != "samsung galaxy s21":
                continue
            
            # Clue 1 and its bi-conditional: The person who uses an iPhone 13 is Alice.
            valid = True
            for i in range(6):
                if phone[i] == "iphone 13" and people[i] != "Alice":
                    valid = False
                    break
                if people[i] == "Alice" and phone[i] != "iphone 13":
                    valid = False
                    break
            if not valid:
                continue

            # Clue 6: There is one house between Bob and Carol.
            if abs(people.index("Bob") - people.index("Carol")) != 2:
                continue

            # Clue 9: Alice is somewhere to the left of Carol.
            if people.index("Alice") >= people.index("Carol"):
                continue

            # All constraints satisfied; store the solution.
            solution = {
                "solution": {
                    "header": ["House", "Name", "PhoneModel"],
                    "rows": [
                        ["1", people[0], phone[0]],
                        ["2", people[1], phone[1]],
                        ["3", people[2], phone[2]],
                        ["4", people[3], phone[3]],
                        ["5", people[4], phone[4]],
                        ["6", people[5], phone[5]]
                    ]
                }
            }
            break
        if solution is not None:
            break
    return solution

if __name__ == "__main__":
    sol = solve()
    print(json.dumps(sol))