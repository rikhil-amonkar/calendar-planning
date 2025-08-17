import json
from itertools import permutations

# Define all possible values
names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights = ['average', 'very tall', 'very short', 'short', 'tall']
cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

solution = None

# Iterate through all possible permutations for each attribute
for name_perm in permutations(names):
    for height_perm in permutations(heights):
        for cigar_perm in permutations(cigars):
            for smoothie_perm in permutations(smoothies):
                for phone_perm in permutations(phones):
                    # Create a list of houses
                    houses = []
                    for i in range(5):
                        house = {
                            'House': i + 1,
                            'Name': name_perm[i],
                            'Height': height_perm[i],
                            'Cigar': cigar_perm[i],
                            'Smoothie': smoothie_perm[i],
                            'PhoneModel': phone_perm[i]
                        }
                        houses.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # Clue 1: Prince smoker is Desert smoothie lover
                    prince_index = cigar_perm.index('prince')
                    if smoothie_perm[prince_index] != 'desert':
                        valid = False
                    
                    # Clue 2: One house between Eric and Alice
                    eric_house = None
                    alice_house = None
                    for i in range(5):
                        if name_perm[i] == 'Eric':
                            eric_house = i + 1
                        if name_perm[i] == 'Alice':
                            alice_house = i + 1
                    if abs(eric_house - alice_house) != 2:
                        valid = False
                    
                    # Clue 3: Short person smokes Blends
                    short_index = height_perm.index('short')
                    if cigar_perm[short_index] != 'blends':
                        valid = False
                    
                    # Clue 4: iPhone 13 is directly left of Blue Master
                    iphone_index = phone_perm.index('iphone 13')
                    if iphone_index + 1 >= 5 or cigar_perm[iphone_index + 1] != 'blue master':
                        valid = False
                    
                    # Clue 5: Average height is Dunhill smoker
                    average_index = height_perm.index('average')
                    if cigar_perm[average_index] != 'dunhill':
                        valid = False
                    
                    # Clue 6: Eric is very tall
                    if height_perm[name_perm.index('Eric')] != 'very tall':
                        valid = False
                    
                    # Clue 7: Arnold is directly left of Huawei P50
                    arnold_index = name_perm.index('Arnold')
                    if arnold_index + 1 >= 5 or phone_perm[arnold_index + 1] != 'huawei p50':
                        valid = False
                    
                    # Clue 8: Bob is not in the fourth house
                    if name_perm[3] == 'Bob':
                        valid = False
                    
                    # Clue 9: Eric is directly left of Cherry smoothie
                    if eric_house + 1 > 5 or smoothie_perm[eric_house] != 'cherry':
                        valid = False
                    
                    # Clue 10: Bob is Dunhill smoker
                    if cigar_perm[name_perm.index('Bob')] != 'dunhill':
                        valid = False
                    
                    # Clue 11: Dragonfruit smoothie lover is Bob
                    if smoothie_perm[name_perm.index('Bob')] != 'dragonfruit':
                        valid = False
                    
                    # Clue 12: iPhone 13 and OnePlus 9 are next to each other
                    iphone_index = phone_perm.index('iphone 13')
                    oneplus_index = phone_perm.index('oneplus 9')
                    if abs(iphone_index - oneplus_index) != 1:
                        valid = False
                    
                    # Clue 13: Samsung Galaxy S21 user is short
                    samsung_index = phone_perm.index('samsung galaxy s21')
                    if height_perm[samsung_index] != 'short':
                        valid = False
                    
                    # Clue 14: Two houses between very tall (Eric) and Dragonfruit lover (Bob)
                    very_tall_index = height_perm.index('very tall')
                    bob_index = name_perm.index('Bob')
                    if abs(very_tall_index - bob_index) != 3:
                        valid = False
                    
                    # Clue 15: Eric's phone is iPhone 13
                    if phone_perm[name_perm.index('Eric')] != 'iphone 13':
                        valid = False
                    
                    # Clue 16: Desert is left of Lime
                    desert_index = smoothie_perm.index('desert')
                    lime_index = smoothie_perm.index('lime')
                    if desert_index >= lime_index:
                        valid = False
                    
                    # Clue 17: Arnold and very short are next to each other
                    arnold_index = name_perm.index('Arnold')
                    very_short_index = height_perm.index('very short')
                    if abs(arnold_index - very_short_index) != 1:
                        valid = False
                    
                    if valid:
                        solution = houses
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break
    if solution:
        break

# Format the solution as JSON
json_output = {
    "solution": {
        "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
        "rows": []
    }
}

for house in solution:
    row = [
        str(house['House']),
        house['Name'],
        house['Height'],
        house['Cigar'],
        house['Smoothie'],
        house['PhoneModel']
    ]
    json_output['solution']['rows'].append(row)

# Print the JSON output
print(json.dumps(json_output, indent=2))