import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for cigar_perm in permutations(cigars):
                for height_perm in permutations(heights):
                    for phone_perm in permutations(phones):
                        # Create a list of houses with all attributes
                        houses = [
                            {
                                'House': '1',
                                'Name': name_perm[0],
                                'Smoothie': smoothie_perm[0],
                                'Cigar': cigar_perm[0],
                                'Height': height_perm[0],
                                'PhoneModel': phone_perm[0]
                            },
                            {
                                'House': '2',
                                'Name': name_perm[1],
                                'Smoothie': smoothie_perm[1],
                                'Cigar': cigar_perm[1],
                                'Height': height_perm[1],
                                'PhoneModel': phone_perm[1]
                            },
                            {
                                'House': '3',
                                'Name': name_perm[2],
                                'Smoothie': smoothie_perm[2],
                                'Cigar': cigar_perm[2],
                                'Height': height_perm[2],
                                'PhoneModel': phone_perm[2]
                            },
                            {
                                'House': '4',
                                'Name': name_perm[3],
                                'Smoothie': smoothie_perm[3],
                                'Cigar': cigar_perm[3],
                                'Height': height_perm[3],
                                'PhoneModel': phone_perm[3]
                            }
                        ]
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The Dragonfruit smoothie lover is Eric.
                        for house in houses:
                            if house['Smoothie'] == 'dragonfruit' and house['Name'] != 'Eric':
                                valid = False
                            if house['Name'] == 'Eric' and house['Smoothie'] != 'dragonfruit':
                                valid = False
                        
                        # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
                        for house in houses:
                            if house['Cigar'] == 'dunhill' and house['Smoothie'] != 'cherry':
                                valid = False
                            if house['Smoothie'] == 'cherry' and house['Cigar'] != 'dunhill':
                                valid = False
                        
                        # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
                        s21_pos = None
                        iphone_pos = None
                        for i, house in enumerate(houses):
                            if house['PhoneModel'] == 'samsung galaxy s21':
                                s21_pos = i
                            if house['PhoneModel'] == 'iphone 13':
                                iphone_pos = i
                        if s21_pos is None or iphone_pos is None or s21_pos + 1 != iphone_pos:
                            valid = False
                        
                        # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
                        dunhill_pos = None
                        very_short_pos = None
                        for i, house in enumerate(houses):
                            if house['Cigar'] == 'dunhill':
                                dunhill_pos = i
                            if house['Height'] == 'very short':
                                very_short_pos = i
                        if dunhill_pos is None or very_short_pos is None or dunhill_pos <= very_short_pos:
                            valid = False
                        
                        # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
                        desert_pos = None
                        watermelon_pos = None
                        for i, house in enumerate(houses):
                            if house['Smoothie'] == 'desert':
                                desert_pos = i
                            if house['Smoothie'] == 'watermelon':
                                watermelon_pos = i
                        if desert_pos is not None and watermelon_pos is not None and watermelon_pos <= desert_pos:
                            valid = False
                        
                        # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
                        for house in houses:
                            if house['Cigar'] == 'prince' and house['PhoneModel'] != 'oneplus 9':
                                valid = False
                            if house['PhoneModel'] == 'oneplus 9' and house['Cigar'] != 'prince':
                                valid = False
                        
                        # Clue 7: The person who is tall is in the third house.
                        if houses[2]['Height'] != 'tall':
                            valid = False
                        
                        # Clue 8: The person who is very short is the person who uses an iPhone 13.
                        for house in houses:
                            if house['Height'] == 'very short' and house['PhoneModel'] != 'iphone 13':
                                valid = False
                            if house['PhoneModel'] == 'iphone 13' and house['Height'] != 'very short':
                                valid = False
                        
                        # Clue 9: The person who smokes Blue Master is not in the first house.
                        if houses[0]['Cigar'] == 'blue master':
                            valid = False
                        
                        # Clue 10: The Dunhill smoker is the person who is short.
                        for house in houses:
                            if house['Cigar'] == 'dunhill' and house['Height'] != 'short':
                                valid = False
                            if house['Height'] == 'short' and house['Cigar'] != 'dunhill':
                                valid = False
                        
                        # Clue 11: Peter is not in the third house.
                        if houses[2]['Name'] == 'Peter':
                            valid = False
                        
                        # Clue 12: Arnold is the person who uses a Google Pixel 6.
                        for house in houses:
                            if house['Name'] == 'Arnold' and house['PhoneModel'] != 'google pixel 6':
                                valid = False
                            if house['PhoneModel'] == 'google pixel 6' and house['Name'] != 'Arnold':
                                valid = False
                        
                        # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
                        for house in houses:
                            if house['Smoothie'] == 'dragonfruit' and house['Cigar'] != 'pall mall':
                                valid = False
                            if house['Cigar'] == 'pall mall' and house['Smoothie'] != 'dragonfruit':
                                valid = False
                        
                        if valid:
                            # Prepare the solution in the required format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                                    "rows": [
                                        [
                                            house['House'],
                                            house['Name'],
                                            house['Smoothie'],
                                            house['Cigar'],
                                            house['Height'],
                                            house['PhoneModel']
                                        ] for house in houses
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())