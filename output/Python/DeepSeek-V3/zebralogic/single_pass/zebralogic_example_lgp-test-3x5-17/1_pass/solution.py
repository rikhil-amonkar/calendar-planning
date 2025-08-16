import itertools
import json

def solve_puzzle():
    # Define all possible options for each category
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'average', 'short']
    house_styles = ['colonial', 'ranch', 'victorian']
    car_models = ['tesla model 3', 'toyota camry', 'ford f150']
    
    # Generate all possible permutations for each category
    for name_perm in itertools.permutations(names):
        # Clue 7: Arnold is in the second house
        if name_perm[1] != 'Arnold':
            continue
        
        # Clue 1: Peter is to the right of Eric
        eric_pos = name_perm.index('Eric')
        peter_pos = name_perm.index('Peter')
        if peter_pos <= eric_pos:
            continue
        
        for phone_perm in itertools.permutations(phones):
            # Clue 5: iphone 13 is directly left of google pixel 6
            try:
                iphone_pos = phone_perm.index('iphone 13')
                pixel_pos = phone_perm.index('google pixel 6')
                if pixel_pos != iphone_pos + 1:
                    continue
            except ValueError:
                continue
            
            # Clue 4: short is directly left of samsung galaxy s21
            for height_perm in itertools.permutations(heights):
                try:
                    short_pos = height_perm.index('short')
                    samsung_pos = phone_perm.index('samsung galaxy s21')
                    if samsung_pos != short_pos + 1:
                        continue
                except ValueError:
                    continue
                
                # Clue 9: average height is in the first house
                if height_perm[0] != 'average':
                    continue
                
                for house_perm in itertools.permutations(house_styles):
                    # Clue 2: colonial is in the second house
                    if house_perm[1] != 'colonial':
                        continue
                    
                    # Clue 6: colonial is right of ranch
                    ranch_pos = house_perm.index('ranch')
                    colonial_pos = house_perm.index('colonial')
                    if colonial_pos <= ranch_pos:
                        continue
                    
                    for car_perm in itertools.permutations(car_models):
                        # Clue 3: tesla model 3 is very short
                        try:
                            tesla_pos = car_perm.index('tesla model 3')
                            if height_perm[tesla_pos] != 'very short':
                                continue
                        except ValueError:
                            continue
                        
                        # Clue 8: ford f150 is right of toyota camry
                        camry_pos = car_perm.index('toyota camry')
                        ford_pos = car_perm.index('ford f150')
                        if ford_pos <= camry_pos:
                            continue
                        
                        # All clues satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                "rows": [
                                    ["1", name_perm[0], phone_perm[0], height_perm[0], house_perm[0], car_perm[0]],
                                    ["2", name_perm[1], phone_perm[1], height_perm[1], house_perm[1], car_perm[1]],
                                    ["3", name_perm[2], phone_perm[2], height_perm[2], house_perm[2], car_perm[2]]
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())