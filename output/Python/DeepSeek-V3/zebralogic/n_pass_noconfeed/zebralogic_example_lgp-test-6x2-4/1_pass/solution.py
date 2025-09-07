import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for phone_perm in permutations(phones):
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    'name': name_perm[i],
                    'phone': phone_perm[i]
                }
            
            # Check all constraints
            valid = True
            
            # Clue 1: The person who uses an iPhone 13 is Alice.
            for house, data in assignment.items():
                if data['phone'] == 'iphone 13' and data['name'] != 'Alice':
                    valid = False
                    break
            if not valid:
                continue
                
            # Clue 2: The person who uses a Huawei P50 is in the first house.
            if assignment[1]['phone'] != 'huawei p50':
                continue
                
            # Clue 3: The person who uses a OnePlus 9 is in the sixth house.
            if assignment[6]['phone'] != 'oneplus 9':
                continue
                
            # Clue 4: The person who uses a Google Pixel 6 is not in the second house.
            if assignment[2]['phone'] == 'google pixel 6':
                continue
                
            # Clue 5: The person who uses an iPhone 13 is not in the second house.
            if assignment[2]['phone'] == 'iphone 13':
                continue
                
            # Clue 6: There is one house between Bob and Carol.
            bob_house = None
            carol_house = None
            for house, data in assignment.items():
                if data['name'] == 'Bob':
                    bob_house = house
                if data['name'] == 'Carol':
                    carol_house = house
            if bob_house is None or carol_house is None or abs(bob_house - carol_house) != 2:
                continue
                
            # Clue 7: The person who uses a Huawei P50 is Eric.
            if assignment[1]['name'] != 'Eric':  # From clue 2, we know Huawei P50 is in house 1
                continue
                
            # Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
            if assignment[3]['phone'] != 'xiaomi mi 11':
                continue
                
            # Clue 9: Alice is somewhere to the left of Carol.
            alice_house = None
            carol_house = None
            for house, data in assignment.items():
                if data['name'] == 'Alice':
                    alice_house = house
                if data['name'] == 'Carol':
                    carol_house = house
            if alice_house is None or carol_house is None or alice_house >= carol_house:
                continue
                
            # Clue 10: Arnold is the person who uses a OnePlus 9.
            if assignment[6]['name'] != 'Arnold':  # From clue 3, we know OnePlus 9 is in house 6
                continue
                
            # If we reach here, all constraints are satisfied
            result = {
                "solution": {
                    "header": ["House", "Name", "PhoneModel"],
                    "rows": []
                }
            }
            
            for house in sorted(assignment.keys()):
                data = assignment[house]
                result["solution"]["rows"].append([
                    str(house),
                    data['name'],
                    data['phone']
                ])
            
            return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()