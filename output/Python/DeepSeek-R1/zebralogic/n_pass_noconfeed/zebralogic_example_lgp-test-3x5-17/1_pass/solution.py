import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'average', 'short']
    styles = ['colonial', 'ranch', 'victorian']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']
    
    # Generate all permutations for each attribute, with fixed values based on clues
    name_perms = [p for p in itertools.permutations(names) if p[1] == 'Arnold']
    phone_perms = list(itertools.permutations(phones))
    height_perms = [p for p in itertools.permutations(heights) if p[0] == 'average']
    style_perms = [p for p in itertools.permutations(styles) if p[1] == 'colonial']
    car_perms = list(itertools.permutations(cars))
    
    # Iterate over all combinations of permutations
    for n in name_perms:
        for p in phone_perms:
            for h in height_perms:
                for s in style_perms:
                    for c in car_perms:
                        # Check constraints
                        # Clue 1: Peter is right of Eric
                        if n.index('Peter') <= n.index('Eric'):
                            continue
                            
                        # Clue 3: Tesla owner is very short
                        if c[h.index('very short')] != 'tesla model 3':
                            continue
                            
                        # Clue 4: Short height directly left of Samsung user
                        try:
                            short_index = h.index('short')
                            if short_index not in [0, 1] or p[short_index + 1] != 'samsung galaxy s21':
                                continue
                        except IndexError:
                            continue
                            
                        # Clue 5: iPhone user directly left of Google Pixel user
                        try:
                            iphone_index = p.index('iphone 13')
                            if iphone_index not in [0, 1] or p[iphone_index + 1] != 'google pixel 6':
                                continue
                        except IndexError:
                            continue
                            
                        # Clue 6: Colonial is right of Ranch (colonial is at index1, so ranch must be at index0)
                        if s.index('ranch') >= 1:
                            continue
                            
                        # Clue 8: Ford F150 right of Toyota Camry
                        if c.index('ford f150') <= c.index('toyota camry'):
                            continue
                            
                        # Found valid assignment
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                "rows": [
                                    ["1", n[0], p[0], h[0], s[0], c[0]],
                                    ["2", n[1], p[1], h[1], s[1], c[1]],
                                    ["3", n[2], p[2], h[2], s[2], c[2]]
                                ]
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        return
                        
    print("No solution found")

if __name__ == "__main__":
    main()