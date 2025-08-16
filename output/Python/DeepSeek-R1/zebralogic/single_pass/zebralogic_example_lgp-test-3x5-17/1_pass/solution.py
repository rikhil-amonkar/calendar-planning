import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    house_styles = ['ranch', 'colonial', 'victorian']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']
    height_options = [('short', 'very short'), ('very short', 'short')]
    
    for phone_perm in itertools.permutations(phones):
        for car_perm in itertools.permutations(cars):
            for h_perm in height_options:
                heights = ['average', h_perm[0], h_perm[1]]
                house0 = ['1', names[0], phone_perm[0], heights[0], house_styles[0], car_perm[0]]
                house1 = ['2', names[1], phone_perm[1], heights[1], house_styles[1], car_perm[1]]
                house2 = ['3', names[2], phone_perm[2], heights[2], house_styles[2], car_perm[2]]
                rows = [house0, house1, house2]
                
                c3_ok = True
                for row in rows:
                    if row[5] == 'tesla model 3':
                        if row[3] != 'very short':
                            c3_ok = False
                            break
                if not c3_ok:
                    continue
                
                c4_ok = False
                if house0[3] == 'short' and house1[2] == 'samsung galaxy s21':
                    c4_ok = True
                elif house1[3] == 'short' and house2[2] == 'samsung galaxy s21':
                    c4_ok = True
                if not c4_ok:
                    continue
                
                c5_ok = False
                if house0[2] == 'iphone 13' and house1[2] == 'google pixel 6':
                    c5_ok = True
                elif house1[2] == 'iphone 13' and house2[2] == 'google pixel 6':
                    c5_ok = True
                if not c5_ok:
                    continue
                
                try:
                    idx_toyota = None
                    idx_ford = None
                    for i, row in enumerate(rows):
                        if row[5] == 'toyota camry':
                            idx_toyota = i
                        if row[5] == 'ford f150':
                            idx_ford = i
                    if idx_toyota is None or idx_ford is None:
                        continue
                    if idx_ford > idx_toyota:
                        c8_ok = True
                    else:
                        c8_ok = False
                except:
                    c8_ok = False
                if not c8_ok:
                    continue
                
                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                        "rows": rows
                    }
                }
                print(json.dumps(solution_dict))
                return
                
    print(json.dumps({"solution": {"header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"], "rows": []}}))

if __name__ == '__main__':
    main()