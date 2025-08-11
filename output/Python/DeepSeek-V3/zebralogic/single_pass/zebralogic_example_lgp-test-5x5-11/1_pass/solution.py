import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

    # Initialize all possible positions for each attribute
    for name_order in permutations(names):
        for height_order in permutations(heights):
            for cigar_order in permutations(cigars):
                for smoothie_order in permutations(smoothies):
                    for phone_order in permutations(phones):
                        # Create a dictionary to hold the current assignment
                        assignment = []
                        for i in range(5):
                            house = {
                                'House': str(i+1),
                                'Name': name_order[i],
                                'Height': height_order[i],
                                'Cigar': cigar_order[i],
                                'Smoothie': smoothie_order[i],
                                'Phone': phone_order[i]
                            }
                            assignment.append(house)

                        # Check all constraints
                        valid = True

                        # 1. The Prince smoker is the Desert smoothie lover.
                        prince_smoker = None
                        desert_lover = None
                        for house in assignment:
                            if house['Cigar'] == 'prince':
                                prince_smoker = house
                            if house['Smoothie'] == 'desert':
                                desert_lover = house
                        if prince_smoker != desert_lover:
                            valid = False
                            continue

                        # 2. There is one house between Eric and Alice.
                        eric_pos = None
                        alice_pos = None
                        for i, house in enumerate(assignment):
                            if house['Name'] == 'Eric':
                                eric_pos = i + 1
                            if house['Name'] == 'Alice':
                                alice_pos = i + 1
                        if eric_pos is None or alice_pos is None or abs(eric_pos - alice_pos) != 2:
                            valid = False
                            continue

                        # 3. The person who is short is the person who smokes many unique blends.
                        short_person = None
                        blends_smoker = None
                        for house in assignment:
                            if house['Height'] == 'short':
                                short_person = house
                            if house['Cigar'] == 'blends':
                                blends_smoker = house
                        if short_person != blends_smoker:
                            valid = False
                            continue

                        # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
                        iphone_pos = None
                        blue_master_pos = None
                        for i, house in enumerate(assignment):
                            if house['Phone'] == 'iphone 13':
                                iphone_pos = i
                            if house['Cigar'] == 'blue master':
                                blue_master_pos = i
                        if iphone_pos is None or blue_master_pos is None or blue_master_pos - iphone_pos != 1:
                            valid = False
                            continue

                        # 5. The person who has an average height is the Dunhill smoker.
                        avg_height = None
                        dunhill_smoker = None
                        for house in assignment:
                            if house['Height'] == 'average':
                                avg_height = house
                            if house['Cigar'] == 'dunhill':
                                dunhill_smoker = house
                        if avg_height != dunhill_smoker:
                            valid = False
                            continue

                        # 6. Eric is the person who is very tall.
                        eric_house = None
                        for house in assignment:
                            if house['Name'] == 'Eric':
                                eric_house = house
                        if eric_house is None or eric_house['Height'] != 'very tall':
                            valid = False
                            continue

                        # 7. Arnold is directly left of the person who uses a Huawei P50.
                        arnold_pos = None
                        huawei_pos = None
                        for i, house in enumerate(assignment):
                            if house['Name'] == 'Arnold':
                                arnold_pos = i
                            if house['Phone'] == 'huawei p50':
                                huawei_pos = i
                        if arnold_pos is None or huawei_pos is None or huawei_pos - arnold_pos != 1:
                            valid = False
                            continue

                        # 8. Bob is not in the fourth house.
                        for house in assignment:
                            if house['Name'] == 'Bob' and house['House'] == '4':
                                valid = False
                                break
                        if not valid:
                            continue

                        # 9. Eric is directly left of the person who likes Cherry smoothies.
                        cherry_pos = None
                        for i, house in enumerate(assignment):
                            if house['Smoothie'] == 'cherry':
                                cherry_pos = i
                        if cherry_pos is None or cherry_pos - eric_pos + 1 != 1:
                            valid = False
                            continue

                        # 10. Bob is the Dunhill smoker.
                        bob_house = None
                        for house in assignment:
                            if house['Name'] == 'Bob':
                                bob_house = house
                        if bob_house is None or bob_house['Cigar'] != 'dunhill':
                            valid = False
                            continue

                        # 11. The Dragonfruit smoothie lover is Bob.
                        if bob_house is None or bob_house['Smoothie'] != 'dragonfruit':
                            valid = False
                            continue

                        # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
                        iphone_pos = None
                        oneplus_pos = None
                        for i, house in enumerate(assignment):
                            if house['Phone'] == 'iphone 13':
                                iphone_pos = i
                            if house['Phone'] == 'oneplus 9':
                                oneplus_pos = i
                        if iphone_pos is None or oneplus_pos is None or abs(iphone_pos - oneplus_pos) != 1:
                            valid = False
                            continue

                        # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
                        samsung_user = None
                        for house in assignment:
                            if house['Phone'] == 'samsung galaxy s21':
                                samsung_user = house
                        if samsung_user is None or samsung_user['Height'] != 'short':
                            valid = False
                            continue

                        # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
                        very_tall_pos = None
                        dragonfruit_pos = None
                        for i, house in enumerate(assignment):
                            if house['Height'] == 'very tall':
                                very_tall_pos = i + 1
                            if house['Smoothie'] == 'dragonfruit':
                                dragonfruit_pos = i + 1
                        if very_tall_pos is None or dragonfruit_pos is None or abs(very_tall_pos - dragonfruit_pos) != 3:
                            valid = False
                            continue

                        # 15. The person who uses an iPhone 13 is Eric.
                        for house in assignment:
                            if house['Phone'] == 'iphone 13' and house['Name'] != 'Eric':
                                valid = False
                                break
                        if not valid:
                            continue

                        # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
                        desert_pos = None
                        lime_pos = None
                        for i, house in enumerate(assignment):
                            if house['Smoothie'] == 'desert':
                                desert_pos = i
                            if house['Smoothie'] == 'lime':
                                lime_pos = i
                        if desert_pos is None or lime_pos is None or desert_pos >= lime_pos:
                            valid = False
                            continue

                        # 17. Arnold and the person who is very short are next to each other.
                        arnold_pos = None
                        very_short_pos = None
                        for i, house in enumerate(assignment):
                            if house['Name'] == 'Arnold':
                                arnold_pos = i
                            if house['Height'] == 'very short':
                                very_short_pos = i
                        if arnold_pos is None or very_short_pos is None or abs(arnold_pos - very_short_pos) != 1:
                            valid = False
                            continue

                        # If all constraints are satisfied, return the solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Height", "Cigar", "Smoothie", "Phone"],
                                    "rows": []
                                }
                            }
                            for house in assignment:
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Height'],
                                    house['Cigar'],
                                    house['Smoothie'],
                                    house['Phone']
                                ]
                                solution["solution"]["rows"].append(row)
                            return solution

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))