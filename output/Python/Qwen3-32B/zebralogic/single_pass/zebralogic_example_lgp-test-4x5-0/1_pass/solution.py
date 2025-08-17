import itertools
import json

# Define the categories
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

solution = None

for names_p in itertools.permutations(names):
    for smoothies_p in itertools.permutations(smoothies):
        for cigars_p in itertools.permutations(cigars):
            for heights_p in itertools.permutations(heights):
                for phones_p in itertools.permutations(phones):
                    # Clue 1: Dragonfruit lover is Eric
                    dragonfruit_idx = smoothies_p.index('dragonfruit')
                    if names_p[dragonfruit_idx] != 'Eric':
                        continue
                    # Clue 2: Dunhill smoker likes Cherry
                    dunhill_idx = cigars_p.index('dunhill')
                    if smoothies_p[dunhill_idx] != 'cherry':
                        continue
                    # Clue 3: Samsung directly left of iPhone
                    try:
                        samsung_idx = phones_p.index('samsung galaxy s21')
                        iphone_idx = phones_p.index('iphone 13')
                        if iphone_idx != samsung_idx + 1:
                            continue
                    except ValueError:
                        continue
                    # Clue 4: Dunhill is right of very short
                    very_short_idx = heights_p.index('very short')
                    if dunhill_idx <= very_short_idx:
                        continue
                    # Clue 5: Watermelon right of Desert
                    desert_idx = smoothies_p.index('desert')
                    watermelon_idx = smoothies_p.index('watermelon')
                    if watermelon_idx <= desert_idx:
                        continue
                    # Clue 6: Prince smoker uses OnePlus 9
                    prince_idx = cigars_p.index('prince')
                    if phones_p[prince_idx] != 'oneplus 9':
                        continue
                    # Clue 7: Tall is in house 3
                    if heights_p[2] != 'tall':
                        continue
                    # Clue 8: iPhone 13 user is very short
                    iphone_idx = phones_p.index('iphone 13')
                    if heights_p[iphone_idx] != 'very short':
                        continue
                    # Clue 9: Blue Master not in first house
                    blue_master_idx = cigars_p.index('blue master')
                    if blue_master_idx == 0:
                        continue
                    # Clue 10: Dunhill smoker is short
                    if heights_p[dunhill_idx] != 'short':
                        continue
                    # Clue 11: Peter not in third house
                    if names_p[2] == 'Peter':
                        continue
                    # Clue 12: Arnold uses Google Pixel 6
                    arnold_idx = names_p.index('Arnold')
                    if phones_p[arnold_idx] != 'google pixel 6':
                        continue
                    # Clue 13: Dragonfruit lover is Pall Mall
                    if cigars_p[dragonfruit_idx] != 'pall mall':
                        continue
                    
                    # Build solution
                    rows = []
                    for i in range(4):
                        house_num = str(i + 1)
                        name = names_p[i]
                        smoothie = smoothies_p[i]
                        cigar = cigars_p[i]
                        height = heights_p[i]
                        phone = phones_p[i]
                        rows.append([house_num, name, smoothie, cigar, height, phone])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                            "rows": rows
                        }
                    }
                    print(json.dumps(solution))
                    exit()