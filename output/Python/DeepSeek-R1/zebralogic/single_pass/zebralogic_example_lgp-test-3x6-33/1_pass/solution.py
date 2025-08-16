import itertools
import json

def main():
    domains = {
        'Name': ['Arnold', 'Eric', 'Peter'],
        'Flower': ['carnations', 'lilies', 'daffodils'],
        'HairColor': ['black', 'brown', 'blonde'],
        'FavoriteSport': ['soccer', 'basketball', 'tennis'],
        'HouseStyle': ['colonial', 'ranch', 'victorian'],
        'Pet': ['fish', 'dog', 'cat']
    }
    
    found_solution = None
    found = False
    for name_perm in itertools.permutations(domains['Name']):
        for flower_perm in itertools.permutations(domains['Flower']):
            if flower_perm[0] != 'carnations' or flower_perm[1] != 'daffodils' or flower_perm[2] != 'lilies':
                continue
            for hair_perm in itertools.permutations(domains['HairColor']):
                if hair_perm[1] != 'blonde':
                    continue
                for sport_perm in itertools.permutations(domains['FavoriteSport']):
                    if sport_perm[2] != 'soccer':
                        continue
                    for style_perm in itertools.permutations(domains['HouseStyle']):
                        if style_perm[2] != 'colonial':
                            continue
                        for pet_perm in itertools.permutations(domains['Pet']):
                            if pet_perm[2] != 'cat':
                                continue
                            houses = [
                                [name_perm[0], flower_perm[0], hair_perm[0], sport_perm[0], style_perm[0], pet_perm[0]],
                                [name_perm[1], flower_perm[1], hair_perm[1], sport_perm[1], style_perm[1], pet_perm[1]],
                                [name_perm[2], flower_perm[2], hair_perm[2], sport_perm[2], style_perm[2], pet_perm[2]]
                            ]
                            if check_solution(houses):
                                found_solution = houses
                                found = True
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    
    if found_solution:
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": [
                    ["1"] + found_solution[0],
                    ["2"] + found_solution[1],
                    ["3"] + found_solution[2]
                ]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {}}))

def check_solution(houses):
    if houses[1][2] != 'blonde':
        return False
    if houses[1][1] != 'daffodils':
        return False
    if houses[0][1] != 'carnations':
        return False
    if houses[2][3] != 'soccer':
        return False
    if houses[2][4] != 'colonial':
        return False
    if houses[2][5] != 'cat':
        return False
    
    peter_found = False
    for house in houses:
        if house[0] == 'Peter':
            if house[3] != 'basketball':
                return False
            peter_found = True
    if not peter_found:
        return False
    
    arnold_found = False
    for i in range(2):
        if houses[i][0] == 'Arnold':
            if houses[i+1][4] != 'ranch':
                return False
            arnold_found = True
    if not arnold_found:
        return False
    
    dog_found = False
    for house in houses:
        if house[5] == 'dog':
            if house[3] != 'basketball':
                return False
            dog_found = True
    if not dog_found:
        return False
    
    arnold_index = None
    black_index = None
    for i, house in enumerate(houses):
        if house[0] == 'Arnold':
            arnold_index = i
        if house[2] == 'black':
            black_index = i
    if arnold_index is None or black_index is None:
        return False
    if arnold_index >= black_index:
        return False
    
    return True

if __name__ == "__main__":
    main()