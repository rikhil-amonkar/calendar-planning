import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'average', 'short']
    house_styles = ['colonial', 'ranch', 'victorian']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']
    
    # House positions
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        # Clue 7: Arnold is in the second house
        if name_perm[1] != 'Arnold':
            continue
        
        for phone_perm in permutations(phones):
            # Clue 5: iphone 13 is directly left of google pixel 6
            iphone_pos = None
            pixel_pos = None
            for i in range(3):
                if phone_perm[i] == 'iphone 13':
                    iphone_pos = i
                if phone_perm[i] == 'google pixel 6':
                    pixel_pos = i
            if iphone_pos is None or pixel_pos is None or (iphone_pos + 1) != pixel_pos:
                continue
            
            for height_perm in permutations(heights):
                # Clue 9: average height is in the first house
                if height_perm[0] != 'average':
                    continue
                
                # Clue 3: tesla model 3 owner is very short
                # We'll check this after car permutations
                
                for house_style_perm in permutations(house_styles):
                    # Clue 2: colonial is in the second house
                    if house_style_perm[1] != 'colonial':
                        continue
                    
                    # Clue 6: colonial is right of ranch
                    ranch_pos = None
                    colonial_pos = 1  # from clue 2
                    for i in range(3):
                        if house_style_perm[i] == 'ranch':
                            ranch_pos = i
                    if ranch_pos is None or ranch_pos >= colonial_pos:
                        continue
                    
                    for car_perm in permutations(cars):
                        # Clue 3: tesla model 3 owner is very short
                        tesla_pos = None
                        very_short_pos = None
                        for i in range(3):
                            if car_perm[i] == 'tesla model 3':
                                tesla_pos = i
                            if height_perm[i] == 'very short':
                                very_short_pos = i
                        if tesla_pos is None or very_short_pos is None or tesla_pos != very_short_pos:
                            continue
                        
                        # Clue 8: ford f150 is right of toyota camry
                        camry_pos = None
                        ford_pos = None
                        for i in range(3):
                            if car_perm[i] == 'toyota camry':
                                camry_pos = i
                            if car_perm[i] == 'ford f150':
                                ford_pos = i
                        if camry_pos is None or ford_pos is None or ford_pos <= camry_pos:
                            continue
                        
                        # Clue 4: short is directly left of samsung galaxy s21
                        short_pos = None
                        samsung_pos = None
                        for i in range(3):
                            if height_perm[i] == 'short':
                                short_pos = i
                            if phone_perm[i] == 'samsung galaxy s21':
                                samsung_pos = i
                        if short_pos is None or samsung_pos is None or (short_pos + 1) != samsung_pos:
                            continue
                        
                        # Clue 1: Peter is right of Eric
                        eric_pos = None
                        peter_pos = None
                        for i in range(3):
                            if name_perm[i] == 'Eric':
                                eric_pos = i
                            if name_perm[i] == 'Peter':
                                peter_pos = i
                        if eric_pos is None or peter_pos is None or peter_pos <= eric_pos:
                            continue
                        
                        # All clues satisfied, construct solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Phone", "Height", "House Style", "Car"],
                                "rows": []
                            }
                        }
                        for i in range(3):
                            row = [
                                str(i+1),
                                name_perm[i],
                                phone_perm[i],
                                height_perm[i],
                                house_style_perm[i],
                                car_perm[i]
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))