import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
    phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']

    for name_perm in permutations(names):
        # Clue 18: Alice is in the first house.
        if name_perm[0] != 'Alice':
            continue
            
        for phone_perm in permutations(phones):
            # Clue 1: The person who uses a OnePlus 9 is in the second house.
            if phone_perm[1] != 'oneplus 9':
                continue
                
            for cigar_perm in permutations(cigars):
                for flower_perm in permutations(flowers):
                    # Clue 3: Carol is the person who loves a carnations arrangement.
                    carol_index = name_perm.index('Carol')
                    if flower_perm[carol_index] != 'carnations':
                        continue
                        
                    # Clue 8: There are two houses between Carol and the person who loves a bouquet of daffodils.
                    daffodils_index = flower_perm.index('daffodils')
                    if abs(carol_index - daffodils_index) != 3:
                        continue
                        
                    # Clue 17: The person who loves the vase of tulips is Bob.
                    bob_index = name_perm.index('Bob')
                    if flower_perm[bob_index] != 'tulips':
                        continue
                        
                    # Clue 14: The person who loves the boquet of iris is somewhere to the left of Eric.
                    eric_index = name_perm.index('Eric')
                    iris_index = flower_perm.index('iris')
                    if iris_index >= eric_index:
                        continue
                        
                    for color_perm in permutations(colors):
                        # Clue 4: The person who loves purple is directly left of the person partial to Pall Mall.
                        purple_index = color_perm.index('purple')
                        pall_mall_index = cigar_perm.index('pall mall')
                        if purple_index + 1 != pall_mall_index:
                            continue
                            
                        # Clue 5: The person whose favorite color is green is the person who smokes Blue Master.
                        green_index = color_perm.index('green')
                        blue_master_index = cigar_perm.index('blue master')
                        if green_index != blue_master_index:
                            continue
                            
                        # Clue 6: The person who loves yellow and the person who loves blue are next to each other.
                        yellow_index = color_perm.index('yellow')
                        blue_index = color_perm.index('blue')
                        if abs(yellow_index - blue_index) != 1:
                            continue
                            
                        # Clue 12: The person who uses a Huawei P50 is directly left of the person who loves white.
                        huawei_index = phone_perm.index('huawei p50')
                        white_index = color_perm.index('white')
                        if huawei_index + 1 != white_index:
                            continue
                            
                        # Clue 16: The person who loves blue is Peter.
                        peter_index = name_perm.index('Peter')
                        if color_perm[peter_index] != 'blue':
                            continue
                            
                        for sport_perm in permutations(sports):
                            # Clue 2: The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
                            xiaomi_index = phone_perm.index('xiaomi mi 11')
                            if xiaomi_index >= huawei_index:
                                continue
                                
                            # Clue 7: Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
                            samsung_index = phone_perm.index('samsung galaxy s21')
                            if eric_index <= samsung_index:
                                continue
                                
                            # Clue 9: The Prince smoker is the person who loves basketball.
                            prince_index = cigar_perm.index('prince')
                            basketball_index = sport_perm.index('basketball')
                            if prince_index != basketball_index:
                                continue
                                
                            # Clue 10: The Dunhill smoker is the person who loves volleyball.
                            dunhill_index = cigar_perm.index('dunhill')
                            volleyball_index = sport_perm.index('volleyball')
                            if dunhill_index != volleyball_index:
                                continue
                                
                            # Clue 11: The person who loves swimming is the person who uses a Google Pixel 6.
                            swimming_index = sport_perm.index('swimming')
                            pixel_index = phone_perm.index('google pixel 6')
                            if swimming_index != pixel_index:
                                continue
                                
                            # Clue 13: The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
                            oneplus_index = phone_perm.index('oneplus 9')
                            roses_index = flower_perm.index('roses')
                            if abs(oneplus_index - roses_index) != 1:
                                continue
                                
                            # Clue 15: The Dunhill smoker is Peter.
                            if cigar_perm[peter_index] != 'dunhill':
                                continue
                                
                            # Clue 19: The person who loves baseball is directly left of the person who smokes Blue Master.
                            baseball_index = sport_perm.index('baseball')
                            if baseball_index + 1 != blue_master_index:
                                continue
                                
                            # Clue 20: The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
                            blends_index = cigar_perm.index('blends')
                            if pixel_index <= blends_index:
                                continue
                                
                            # Clue 21: The person who loves soccer is Carol.
                            if sport_perm[carol_index] != 'soccer':
                                continue
                                
                            # Clue 22: The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
                            if carol_index + 1 != blends_index:
                                continue
                                
                            # Clue 23: Eric is the person who smokes many unique blends.
                            if cigar_perm[eric_index] != 'blends':
                                continue
                                
                            # Clue 24: The person who loves volleyball is the person who uses an iPhone 13.
                            iphone_index = phone_perm.index('iphone 13')
                            if volleyball_index != iphone_index:
                                continue
                            
                            # All constraints satisfied, build solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(6):
                                row = [
                                    str(i + 1),
                                    name_perm[i],
                                    phone_perm[i],
                                    cigar_perm[i],
                                    flower_perm[i],
                                    color_perm[i],
                                    sport_perm[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
                            
    print('{"solution": {"header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"], "rows": []}}')

if __name__ == "__main__":
    main()