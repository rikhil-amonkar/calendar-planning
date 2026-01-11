import itertools
import json

def check_constraints(houses):
    # Unpack houses for easier access
    h1, h2, h3 = houses
    
    # Clue 1: Peter is somewhere to the right of Eric.
    if h1['Name'] == 'Peter' and h2['Name'] == 'Eric':
        return False
    if h1['Name'] == 'Peter' and h3['Name'] == 'Eric':
        return False
    if h2['Name'] == 'Peter' and h3['Name'] == 'Eric':
        return False
    
    # Clue 2: The person living in a colonial-style house is in the second house.
    if h2['HouseStyle'] != 'colonial':
        return False
    
    # Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
    if any(house['CarModel'] == 'tesla model 3' and house['Height'] != 'very short' for house in houses):
        return False
    
    # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    if h1['Height'] == 'short' and h2['PhoneModel'] != 'samsung galaxy s21':
        return False
    if h2['Height'] == 'short' and h3['PhoneModel'] != 'samsung galaxy s21':
        return False
    
    # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    if h1['PhoneModel'] == 'iphone 13' and h2['PhoneModel'] != 'google pixel 6':
        return False
    if h2['PhoneModel'] == 'iphone 13' and h3['PhoneModel'] != 'google pixel 6':
        return False
    
    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    if h1['HouseStyle'] == 'colonial' and h2['HouseStyle'] == 'ranch':
        return False
    if h1['HouseStyle'] == 'colonial' and h3['HouseStyle'] == 'ranch':
        return False
    if h2['HouseStyle'] == 'colonial' and h3['HouseStyle'] == 'ranch':
        return False
    
    # Clue 7: Arnold is in the second house.
    if h2['Name'] != 'Arnold':
        return False
    
    # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    if h1['CarModel'] == 'ford f150' and h2['CarModel'] == 'toyota camry':
        return False
    if h1['CarModel'] == 'ford f150' and h3['CarModel'] == 'toyota camry':
        return False
    if h2['CarModel'] == 'ford f150' and h3['CarModel'] == 'toyota camry':
        return False
    
    # Clue 9: The person who has an average height is in the first house.
    if h1['Height'] != 'average':
        return False
    
    return True

def solve_puzzle():
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'average', 'short']
    house_styles = ['colonial', 'ranch', 'victorian']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']
    
    # Generate all permutations for each category
    for name_perm in itertools.permutations(names):
        for phone_perm in itertools.permutations(phones):
            for height_perm in itertools.permutations(heights):
                for house_style_perm in itertools.permutations(house_styles):
                    for car_perm in itertools.permutations(cars):
                        # Create houses based on current permutation
                        houses = [
                            {'Name': name_perm[0], 'PhoneModel': phone_perm[0], 'Height': height_perm[0], 'HouseStyle': house_style_perm[0], 'CarModel': car_perm[0]},
                            {'Name': name_perm[1], 'PhoneModel': phone_perm[1], 'Height': height_perm[1], 'HouseStyle': house_style_perm[1], 'CarModel': car_perm[1]},
                            {'Name': name_perm[2], 'PhoneModel': phone_perm[2], 'Height': height_perm[2], 'HouseStyle': house_style_perm[2], 'CarModel': car_perm[2]}
                        ]
                        
                        # Check if this configuration satisfies all constraints
                        if check_constraints(houses):
                            # Format the solution as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                    "rows": [
                                        ["1", houses[0]['Name'], houses[0]['PhoneModel'], houses[0]['Height'], houses[0]['HouseStyle'], houses[0]['CarModel']],
                                        ["2", houses[1]['Name'], houses[1]['PhoneModel'], houses[1]['Height'], houses[1]['HouseStyle'], houses[1]['CarModel']],
                                        ["3", houses[2]['Name'], houses[2]['PhoneModel'], houses[2]['Height'], houses[2]['HouseStyle'], houses[2]['CarModel']]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())