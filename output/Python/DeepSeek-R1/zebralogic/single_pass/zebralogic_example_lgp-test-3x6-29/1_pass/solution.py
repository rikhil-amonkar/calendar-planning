import itertools
import json

def main():
    attributes = {
        'name': ['Arnold', 'Peter', 'Eric'],
        'animal': ['bird', 'horse', 'cat'],
        'birthday_month': ['jan', 'sept', 'april'],
        'hobby': ['photography', 'cooking', 'gardening'],
        'drink': ['milk', 'water', 'tea'],
        'hair_color': ['black', 'brown', 'blonde']
    }
    
    perms = {}
    for key in attributes:
        perms[key] = list(itertools.permutations(attributes[key]))
    
    solution_found = None
    for name_perm in perms['name']:
        if name_perm[0] == 'Eric':
            continue
        for animal_perm in perms['animal']:
            if animal_perm[1] != 'cat':
                continue
            for bm_perm in perms['birthday_month']:
                if bm_perm[2] != 'april':
                    continue
                for hobby_perm in perms['hobby']:
                    if hobby_perm[1] != 'cooking':
                        continue
                    for drink_perm in perms['drink']:
                        for hair_perm in perms['hair_color']:
                            if hair_perm[1] != 'brown':
                                continue
                            
                            houses = []
                            for i in range(3):
                                house = {
                                    'name': name_perm[i],
                                    'animal': animal_perm[i],
                                    'birthday_month': bm_perm[i],
                                    'hobby': hobby_perm[i],
                                    'drink': drink_perm[i],
                                    'hair_color': hair_perm[i]
                                }
                                houses.append(house)
                            
                            valid = True
                            for i in range(3):
                                if houses[i]['hair_color'] == 'brown' and houses[i]['hobby'] != 'cooking':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            blonde_index = None
                            milk_index = None
                            for i in range(3):
                                if houses[i]['hair_color'] == 'blonde':
                                    blonde_index = i
                                if houses[i]['drink'] == 'milk':
                                    milk_index = i
                            if blonde_index is None or milk_index is None or blonde_index >= milk_index:
                                continue
                            
                            for i in range(3):
                                if houses[i]['hobby'] == 'gardening' and houses[i]['drink'] != 'milk':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            arnold_found = False
                            for i in range(3):
                                if houses[i]['name'] == 'Arnold':
                                    if houses[i]['animal'] != 'bird':
                                        valid = False
                                        break
                                    else:
                                        arnold_found = True
                            if not valid or not arnold_found:
                                continue
                            
                            for i in range(3):
                                if houses[i]['drink'] == 'water' and houses[i]['hobby'] != 'photography':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            found_sept_left_arnold = False
                            for i in [0, 1]:
                                if houses[i]['birthday_month'] == 'sept':
                                    if i+1 < 3 and houses[i+1]['name'] == 'Arnold':
                                        found_sept_left_arnold = True
                                        break
                            if not found_sept_left_arnold:
                                continue
                            
                            solution_found = houses
                            break
                        if solution_found:
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if solution_found:
        header = ["House", "Name", "Animal", "Birthday Month", "Hobby", "Drink", "Hair Color"]
        rows = []
        for i, house in enumerate(solution_found):
            row = [
                str(i+1),
                house['name'],
                house['animal'],
                house['birthday_month'],
                house['hobby'],
                house['drink'],
                house['hair_color']
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()