import itertools
import json

def satisfies_constraints(candidate):
    # Check clue3: Tesla owner is very short
    for house in candidate:
        if house[4] == 'tesla model 3':
            if house[2] != 'very short':
                return False
    
    # Check clue4: Short height directly left of samsung galaxy s21
    found_clue4 = False
    for i in range(2):
        if candidate[i][2] == 'short' and candidate[i+1][1] == 'samsung galaxy s21':
            found_clue4 = True
            break
    if not found_clue4:
        return False
    
    # Check clue5: iphone 13 directly left of google pixel 6
    found_clue5 = False
    for i in range(2):
        if candidate[i][1] == 'iphone 13' and candidate[i+1][1] == 'google pixel 6':
            found_clue5 = True
            break
    if not found_clue5:
        return False
    
    # Check clue8: Ford F150 to the right of Toyota Camry
    cars = [house[4] for house in candidate]
    try:
        toyota_index = cars.index('toyota camry')
        ford_index = cars.index('ford f150')
    except ValueError:
        return False
    if ford_index <= toyota_index:
        return False
        
    return True

def main():
    attributes = {
        'name': ['Eric', 'Arnold', 'Peter'],
        'phone': ['iphone 13', 'samsung galaxy s21', 'google pixel 6'],
        'height': ['very short', 'short', 'average'],
        'house_style': ['colonial', 'ranch', 'victorian'],
        'car': ['tesla model 3', 'toyota camry', 'ford f150']
    }
    
    # Pre-filter permutations based on known constraints
    name_perms = [('Eric', 'Arnold', 'Peter')]
    style_perms = [('ranch', 'colonial', 'victorian')]
    height_perms = [p for p in itertools.permutations(attributes['height']) if p[0]=='average']
    phone_perms = list(itertools.permutations(attributes['phone']))
    car_perms = list(itertools.permutations(attributes['car']))
    
    for name_p in name_perms:
        for phone_p in phone_perms:
            for height_p in height_perms:
                for style_p in style_perms:
                    for car_p in car_perms:
                        candidate = []
                        for i in range(3):
                            house = (name_p[i], phone_p[i], height_p[i], style_p[i], car_p[i])
                            candidate.append(house)
                        if satisfies_constraints(candidate):
                            sol = {
                                "solution": {
                                    "header": ["House", "Name", "Phone", "Height", "House Style", "Car"],
                                    "rows": []
                                }
                            }
                            for idx, house in enumerate(candidate, start=1):
                                row = [str(idx)] + list(house)
                                sol["solution"]["rows"].append(row)
                            print(json.dumps(sol))
                            return
    print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()