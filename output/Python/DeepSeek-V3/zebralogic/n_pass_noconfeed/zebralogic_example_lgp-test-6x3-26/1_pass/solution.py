import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Precompute some known facts from clues
    # Clue 4: Carol is very tall
    carol_height = 'very tall'
    
    # Clue 8: The person who is tall is Arnold
    arnold_height = 'tall'
    
    # Clue 9: The person who is super tall is in the first house
    house1_height = 'super tall'
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol
    carol_phone = 'xiaomi mi 11'
    
    # Clue 12: The person who is short is in the sixth house
    house6_height = 'short'
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short
    # Since short is in house 6, OnePlus 9 must be in house 5
    house5_phone = 'oneplus 9'
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short
    # Since short is in house 6, Google Pixel 6 could be in house 4 (with house 5 between them)
    # or house 8 (impossible), so Google Pixel 6 must be in house 4
    house4_phone = 'google pixel 6'
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6
    # Google Pixel 6 is in house 4, so very short must be in house 5 or 6
    # But house 6 has short height, so very short must be in house 5
    house5_height = 'very short'
    
    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house
    # We'll handle this in the constraint checking
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for phone_perm in permutations(phones):
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_perm[i],
                        'height': height_perm[i],
                        'phone': phone_perm[i]
                    }
                
                # Check if assignment satisfies all constraints
                valid = True
                
                # Clue 1: Bob is directly left of the person who is tall
                bob_found = False
                tall_found = False
                for house in range(1, 6):
                    if assignment[house]['name'] == 'Bob':
                        bob_found = True
                        if assignment[house + 1]['height'] == 'tall':
                            tall_found = True
                            break
                if not (bob_found and tall_found):
                    valid = False
                
                # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13
                peter_pos = None
                iphone_pos = None
                for house in houses:
                    if assignment[house]['name'] == 'Peter':
                        peter_pos = house
                    if assignment[house]['phone'] == 'iphone 13':
                        iphone_pos = house
                if peter_pos is None or iphone_pos is None or peter_pos >= iphone_pos:
                    valid = False
                
                # Clue 3: Already satisfied by our precomputation
                if assignment[4]['phone'] != 'google pixel 6' or assignment[5]['height'] != 'very short':
                    valid = False
                
                # Clue 4: Carol is very tall
                carol_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Carol':
                        carol_house = house
                        break
                if carol_house is None or assignment[carol_house]['height'] != 'very tall':
                    valid = False
                
                # Clue 5: Already satisfied by our precomputation
                if assignment[4]['phone'] != 'google pixel 6' or assignment[6]['height'] != 'short':
                    valid = False
                
                # Clue 6: Samsung Galaxy S21 not in first house
                if assignment[1]['phone'] == 'samsung galaxy s21':
                    valid = False
                
                # Clue 7: Already satisfied by our precomputation
                if assignment[5]['phone'] != 'oneplus 9' or assignment[6]['height'] != 'short':
                    valid = False
                
                # Clue 8: The person who is tall is Arnold
                arnold_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Arnold':
                        arnold_house = house
                        break
                if arnold_house is None or assignment[arnold_house]['height'] != 'tall':
                    valid = False
                
                # Clue 9: Super tall in first house
                if assignment[1]['height'] != 'super tall':
                    valid = False
                
                # Clue 10: Xiaomi Mi 11 is Carol
                if assignment[carol_house]['phone'] != 'xiaomi mi 11':
                    valid = False
                
                # Clue 11: Google Pixel 6 is somewhere to the right of Eric
                eric_pos = None
                pixel_pos = None
                for house in houses:
                    if assignment[house]['name'] == 'Eric':
                        eric_pos = house
                    if assignment[house]['phone'] == 'google pixel 6':
                        pixel_pos = house
                if eric_pos is None or pixel_pos is None or eric_pos >= pixel_pos:
                    valid = False
                
                # Clue 12: Short in sixth house
                if assignment[6]['height'] != 'short':
                    valid = False
                
                # Check precomputed values
                if assignment[1]['height'] != 'super tall':
                    valid = False
                if assignment[4]['phone'] != 'google pixel 6':
                    valid = False
                if assignment[5]['phone'] != 'oneplus 9':
                    valid = False
                if assignment[5]['height'] != 'very short':
                    valid = False
                if assignment[6]['height'] != 'short':
                    valid = False
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['name'],
                            assignment[house]['height'],
                            assignment[house]['phone']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": []}}')

if __name__ == "__main__":
    main()