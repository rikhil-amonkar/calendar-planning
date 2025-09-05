import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for cigar_perm in permutations(cigars):
                for smoothie_perm in permutations(smoothies):
                    for phone_perm in permutations(phones):
                        # Create assignment for each house (1-5)
                        assignment = []
                        for i in range(5):
                            house = {
                                'house': i + 1,
                                'name': name_perm[i],
                                'height': height_perm[i],
                                'cigar': cigar_perm[i],
                                'smoothie': smoothie_perm[i],
                                'phone': phone_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The Prince smoker is the Desert smoothie lover.
                        prince_cigar = None
                        desert_smoothie = None
                        for house in assignment:
                            if house['cigar'] == 'prince':
                                prince_cigar = house
                            if house['smoothie'] == 'desert':
                                desert_smoothie = house
                        if prince_cigar != desert_smoothie:
                            valid = False
                            continue
                        
                        # Clue 2: There is one house between Eric and Alice.
                        eric_house = None
                        alice_house = None
                        for house in assignment:
                            if house['name'] == 'Eric':
                                eric_house = house
                            if house['name'] == 'Alice':
                                alice_house = house
                        if abs(eric_house['house'] - alice_house['house']) != 2:
                            valid = False
                            continue
                        
                        # Clue 3: The person who is short is the person who smokes blends.
                        short_height = None
                        blends_cigar = None
                        for house in assignment:
                            if house['height'] == 'short':
                                short_height = house
                            if house['cigar'] == 'blends':
                                blends_cigar = house
                        if short_height != blends_cigar:
                            valid = False
                            continue
                        
                        # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
                        iphone_house = None
                        blue_master_house = None
                        for house in assignment:
                            if house['phone'] == 'iphone 13':
                                iphone_house = house
                            if house['cigar'] == 'blue master':
                                blue_master_house = house
                        if not iphone_house or not blue_master_house or iphone_house['house'] + 1 != blue_master_house['house']:
                            valid = False
                            continue
                        
                        # Clue 5: The person who has an average height is the Dunhill smoker.
                        avg_height = None
                        dunhill_cigar = None
                        for house in assignment:
                            if house['height'] == 'average':
                                avg_height = house
                            if house['cigar'] == 'dunhill':
                                dunhill_cigar = house
                        if avg_height != dunhill_cigar:
                            valid = False
                            continue
                        
                        # Clue 6: Eric is the person who is very tall.
                        eric_house = None
                        very_tall = None
                        for house in assignment:
                            if house['name'] == 'Eric':
                                eric_house = house
                            if house['height'] == 'very tall':
                                very_tall = house
                        if eric_house != very_tall:
                            valid = False
                            continue
                        
                        # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
                        arnold_house = None
                        huawei_house = None
                        for house in assignment:
                            if house['name'] == 'Arnold':
                                arnold_house = house
                            if house['phone'] == 'huawei p50':
                                huawei_house = house
                        if not arnold_house or not huawei_house or arnold_house['house'] + 1 != huawei_house['house']:
                            valid = False
                            continue
                        
                        # Clue 8: Bob is not in the fourth house.
                        for house in assignment:
                            if house['name'] == 'Bob' and house['house'] == 4:
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
                        eric_house = None
                        cherry_smoothie = None
                        for house in assignment:
                            if house['name'] == 'Eric':
                                eric_house = house
                            if house['smoothie'] == 'cherry':
                                cherry_smoothie = house
                        if not eric_house or not cherry_smoothie or eric_house['house'] + 1 != cherry_smoothie['house']:
                            valid = False
                            continue
                        
                        # Clue 10: Bob is the Dunhill smoker.
                        bob_house = None
                        dunhill_cigar = None
                        for house in assignment:
                            if house['name'] == 'Bob':
                                bob_house = house
                            if house['cigar'] == 'dunhill':
                                dunhill_cigar = house
                        if bob_house != dunhill_cigar:
                            valid = False
                            continue
                        
                        # Clue 11: The Dragonfruit smoothie lover is Bob.
                        dragonfruit_smoothie = None
                        for house in assignment:
                            if house['smoothie'] == 'dragonfruit':
                                dragonfruit_smoothie = house
                        if dragonfruit_smoothie != bob_house:
                            valid = False
                            continue
                        
                        # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
                        iphone_house = None
                        oneplus_house = None
                        for house in assignment:
                            if house['phone'] == 'iphone 13':
                                iphone_house = house
                            if house['phone'] == 'oneplus 9':
                                oneplus_house = house
                        if not iphone_house or not oneplus_house or abs(iphone_house['house'] - oneplus_house['house']) != 1:
                            valid = False
                            continue
                        
                        # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
                        samsung_phone = None
                        short_height = None
                        for house in assignment:
                            if house['phone'] == 'samsung galaxy s21':
                                samsung_phone = house
                            if house['height'] == 'short':
                                short_height = house
                        if samsung_phone != short_height:
                            valid = False
                            continue
                        
                        # Clue 14: There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
                        very_tall_house = None
                        dragonfruit_house = None
                        for house in assignment:
                            if house['height'] == 'very tall':
                                very_tall_house = house
                            if house['smoothie'] == 'dragonfruit':
                                dragonfruit_house = house
                        if abs(very_tall_house['house'] - dragonfruit_house['house']) != 3:
                            valid = False
                            continue
                        
                        # Clue 15: The person who uses an iPhone 13 is Eric.
                        iphone_house = None
                        eric_house = None
                        for house in assignment:
                            if house['phone'] == 'iphone 13':
                                iphone_house = house
                            if house['name'] == 'Eric':
                                eric_house = house
                        if iphone_house != eric_house:
                            valid = False
                            continue
                        
                        # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
                        desert_house = None
                        lime_house = None
                        for house in assignment:
                            if house['smoothie'] == 'desert':
                                desert_house = house
                            if house['smoothie'] == 'lime':
                                lime_house = house
                        if not desert_house or not lime_house or desert_house['house'] >= lime_house['house']:
                            valid = False
                            continue
                        
                        # Clue 17: Arnold and the person who is very short are next to each other.
                        arnold_house = None
                        very_short_house = None
                        for house in assignment:
                            if house['name'] == 'Arnold':
                                arnold_house = house
                            if house['height'] == 'very short':
                                very_short_house = house
                        if not arnold_house or not very_short_house or abs(arnold_house['house'] - very_short_house['house']) != 1:
                            valid = False
                            continue
                        
                        if valid:
                            # Found the solution, format it as JSON
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                    "rows": []
                                }
                            }
                            
                            for house in sorted(assignment, key=lambda x: x['house']):
                                solution["solution"]["rows"].append([
                                    str(house['house']),
                                    house['name'],
                                    house['height'],
                                    house['cigar'],
                                    house['smoothie'],
                                    house['phone']
                                ])
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print("No solution found")

if __name__ == "__main__":
    main()