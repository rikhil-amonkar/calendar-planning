import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']

    # Initialize possibilities
    solutions = []

    # Generate all possible permutations of names and phones for the houses
    for name_perm in permutations(names):
        for phone_perm in permutations(phones):
            # Create a solution candidate
            candidate = []
            for house in houses:
                candidate.append({
                    'House': str(house),
                    'Name': name_perm[house-1],
                    'PhoneModel': phone_perm[house-1]
                })

            # Check all constraints
            valid = True

            # Constraint 1: iPhone 13 is Alice
            for entry in candidate:
                if entry['PhoneModel'] == 'iphone 13' and entry['Name'] != 'Alice':
                    valid = False
                    break
            if not valid:
                continue

            # Constraint 2: Huawei P50 is in first house
            if candidate[0]['PhoneModel'] != 'huawei p50':
                valid = False
                continue

            # Constraint 3: OnePlus 9 is in sixth house
            if candidate[5]['PhoneModel'] != 'oneplus 9':
                valid = False
                continue

            # Constraint 4: Google Pixel 6 is not in second house
            if candidate[1]['PhoneModel'] == 'google pixel 6':
                valid = False
                continue

            # Constraint 5: iPhone 13 is not in second house
            if candidate[1]['PhoneModel'] == 'iphone 13':
                valid = False
                continue

            # Constraint 6: One house between Bob and Carol
            bob_pos = None
            carol_pos = None
            for i, entry in enumerate(candidate):
                if entry['Name'] == 'Bob':
                    bob_pos = i
                elif entry['Name'] == 'Carol':
                    carol_pos = i
            if bob_pos is None or carol_pos is None or abs(bob_pos - carol_pos) != 2:
                valid = False
                continue

            # Constraint 7: Huawei P50 is Eric
            if candidate[0]['Name'] != 'Eric':
                valid = False
                continue

            # Constraint 8: Xiaomi Mi 11 is in third house
            if candidate[2]['PhoneModel'] != 'xiaomi mi 11':
                valid = False
                continue

            # Constraint 9: Alice is left of Carol
            alice_pos = None
            carol_pos = None
            for i, entry in enumerate(candidate):
                if entry['Name'] == 'Alice':
                    alice_pos = i
                elif entry['Name'] == 'Carol':
                    carol_pos = i
            if alice_pos is None or carol_pos is None or alice_pos >= carol_pos:
                valid = False
                continue

            # Constraint 10: Arnold uses OnePlus 9
            for entry in candidate:
                if entry['Name'] == 'Arnold' and entry['PhoneModel'] != 'oneplus 9':
                    valid = False
                    break
            if not valid:
                continue

            # If all constraints are satisfied, add to solutions
            solutions.append(candidate)

    # Prepare the output
    if solutions:
        solution = solutions[0]
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": []
            }
        }
        for entry in solution:
            output["solution"]["rows"].append([entry['House'], entry['Name'], entry['PhoneModel']])
        return json.dumps(output, indent=2)
    else:
        return json.dumps({"solution": {"header": ["House", "Name", "PhoneModel"], "rows": []}})

print(solve_puzzle())