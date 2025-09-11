import itertools
import json

# Define all possible values for each category
names = ['Eric', 'Peter', 'Arnold', 'Alice']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
heights = ['tall', 'average', 'short', 'very short']
phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

solution_found = False

for names_perm in itertools.permutations(names):
    for smoothies_perm in itertools.permutations(smoothies):
        for cigars_perm in itertools.permutations(cigars):
            for heights_perm in itertools.permutations(heights):
                for phones_perm in itertools.permutations(phones):
                    # Clue 7: Tall in house 3 (index 2)
                    if heights_perm[2] != 'tall':
                        continue
                    # Clue 11: Peter not in third house (index 2)
                    if names_perm[2] == 'Peter':
                        continue
                    # Clue 1: Dragonfruit lover is Eric
                    dragonfruit_idx = smoothies_perm.index('dragonfruit')
                    if names_perm[dragonfruit_idx] != 'Eric':
                        continue
                    # Clue 13: Dragonfruit lover smokes Pall Mall
                    if cigars_perm[dragonfruit_idx] != 'pall mall':
                        continue
                    # Clue 2: Dunhill smoker likes Cherry
                    dunhill_idx = cigars_perm.index('dunhill')
                    if smoothies_perm[dunhill_idx] != 'cherry':
                        continue
                    # Clue 10: Dunhill smoker is short
                    if heights_perm[dunhill_idx] != 'short':
                        continue
                    # Clue 4: Dunhill is to the right of very short
                    very_short_idx = heights_perm.index('very short')
                    if dunhill_idx <= very_short_idx:
                        continue
                    # Clue 5: Watermelon is to the right of Desert
                    watermelon_idx = smoothies_perm.index('watermelon')
                    desert_idx = smoothies_perm.index('desert')
                    if watermelon_idx <= desert_idx:
                        continue
                    # Clue 6: Prince smoker uses OnePlus 9
                    prince_idx = cigars_perm.index('prince')
                    if phones_perm[prince_idx] != 'oneplus 9':
                        continue
                    # Clue 3: Samsung S21 directly left of iPhone 13
                    s21_idx = phones_perm.index('samsung galaxy s21')
                    if s21_idx + 1 >= 4 or phones_perm[s21_idx + 1] != 'iphone 13':
                        continue
                    # Clue 8: very short uses iPhone 13
                    if phones_perm[very_short_idx] != 'iphone 13':
                        continue
                    # Clue 9: Blue Master not in first house (index 0)
                    if cigars_perm[0] == 'blue master':
                        continue
                    # Clue 12: Arnold uses Google Pixel 6
                    arnold_idx = names_perm.index('Arnold')
                    if phones_perm[arnold_idx] != 'google pixel 6':
                        continue
                    
                    # All constraints passed, build the solution
                    rows = []
                    for i in range(4):
                        house = str(i + 1)
                        name = names_perm[i]
                        smoothie = smoothies_perm[i]
                        cigar = cigars_perm[i]
                        height = heights_perm[i]
                        phone = phones_perm[i]
                        rows.append([house, name, smoothie, cigar, height, phone])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                            "rows": rows
                        }
                    }
                    
                    print(json.dumps(solution))
                    solution_found = True
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break