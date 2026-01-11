import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", 
              "oneplus 9", "samsung galaxy s21", "google pixel 6"]
    
    # Generate all possible permutations
    name_perms = permutations(names, 6)
    phone_perms = permutations(phones, 6)
    
    solutions = []
    
    # Brute force search through all combinations
    for name_assignment in name_perms:
        for phone_assignment in phone_perms:
            # Create mapping: house -> (name, phone)
            assignment = {}
            for i in range(6):
                assignment[houses[i]] = (name_assignment[i], phone_assignment[i])
            
            # Check all clues
            valid = True
            
            # 1. The person who uses an iPhone 13 is Alice.
            for house in houses:
                name, phone = assignment[house]
                if phone == "iphone 13" and name != "Alice":
                    valid = False
                    break
                if name == "Alice" and phone != "iphone 13":
                    valid = False
                    break
            if not valid:
                continue
            
            # 2. The person who uses a Huawei P50 is in the first house.
            if assignment[1][1] != "huawei p50":
                continue
            
            # 3. The person who uses a OnePlus 9 is in the sixth house.
            if assignment[6][1] != "oneplus 9":
                continue
            
            # 4. The person who uses a Google Pixel 6 is not in the second house.
            if assignment[2][1] == "google pixel 6":
                continue
            
            # 5. The person who uses an iPhone 13 is not in the second house.
            if assignment[2][1] == "iphone 13":
                continue
            
            # 6. There is one house between Bob and Carol.
            bob_house = None
            carol_house = None
            for house in houses:
                if assignment[house][0] == "Bob":
                    bob_house = house
                if assignment[house][0] == "Carol":
                    carol_house = house
            
            if bob_house is None or carol_house is None:
                continue
            if abs(bob_house - carol_house) != 2:
                continue
            
            # 7. The person who uses a Huawei P50 is Eric.
            if assignment[1][0] != "Eric":
                continue
            
            # 8. The person who uses a Xiaomi Mi 11 is in the third house.
            if assignment[3][1] != "xiaomi mi 11":
                continue
            
            # 9. Alice is somewhere to the left of Carol.
            alice_house = None
            for house in houses:
                if assignment[house][0] == "Alice":
                    alice_house = house
                    break
            if alice_house >= carol_house:
                continue
            
            # 10. Arnold is the person who uses a OnePlus 9.
            if assignment[6][0] != "Arnold":
                continue
            
            # All constraints satisfied
            solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be unique
        rows = []
        for house in sorted(solution.keys()):
            name, phone = solution[house]
            rows.append([str(house), name, phone])
        
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())