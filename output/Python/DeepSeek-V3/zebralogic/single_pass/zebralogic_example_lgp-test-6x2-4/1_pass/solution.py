import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']

    # Initialize possibilities
    solution = None

    # Generate all possible permutations for names and phones
    for name_perm in permutations(names):
        for phone_perm in permutations(phones):
            assignment = list(zip(houses, name_perm, phone_perm))
            valid = True

            # Check all constraints
            # 1. The person who uses an iPhone 13 is Alice.
            iphone_user = next((item for item in assignment if item[2] == 'iphone 13'), None)
            if not iphone_user or iphone_user[1] != 'Alice':
                valid = False
                continue

            # 2. The person who uses a Huawei P50 is in the first house.
            huawei_user = assignment[0]
            if huawei_user[2] != 'huawei p50':
                valid = False
                continue

            # 3. The person who uses a OnePlus 9 is in the sixth house.
            oneplus_user = assignment[5]
            if oneplus_user[2] != 'oneplus 9':
                valid = False
                continue

            # 4. The person who uses a Google Pixel 6 is not in the second house.
            pixel_user_house2 = assignment[1]
            if pixel_user_house2[2] == 'google pixel 6':
                valid = False
                continue

            # 5. The person who uses an iPhone 13 is not in the second house.
            iphone_house = iphone_user[0]
            if iphone_house == 2:
                valid = False
                continue

            # 6. There is one house between Bob and Carol.
            bob_pos = None
            carol_pos = None
            for item in assignment:
                if item[1] == 'Bob':
                    bob_pos = item[0]
                if item[1] == 'Carol':
                    carol_pos = item[0]
            if bob_pos is None or carol_pos is None or abs(bob_pos - carol_pos) != 2:
                valid = False
                continue

            # 7. The person who uses a Huawei P50 is Eric.
            if huawei_user[1] != 'Eric':
                valid = False
                continue

            # 8. The person who uses a Xiaomi Mi 11 is in the third house.
            xiaomi_user = assignment[2]
            if xiaomi_user[2] != 'xiaomi mi 11':
                valid = False
                continue

            # 9. Alice is somewhere to the left of Carol.
            alice_pos = next(item[0] for item in assignment if item[1] == 'Alice')
            carol_pos = next(item[0] for item in assignment if item[1] == 'Carol')
            if alice_pos >= carol_pos:
                valid = False
                continue

            # 10. Arnold is the person who uses a OnePlus 9.
            oneplus_user = assignment[5]
            if oneplus_user[1] != 'Arnold':
                valid = False
                continue

            if valid:
                solution = assignment
                break
        if solution:
            break

    # Format the solution
    if solution:
        rows = []
        for house in solution:
            rows.append([str(house[0]), house[1], house[2]])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Phone"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"solution": {}})

print(solve_puzzle())