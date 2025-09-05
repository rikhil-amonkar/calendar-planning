import itertools
import json

def main():
    attributes = {
        'Name': ['Arnold', 'Eric', 'Peter'],
        'Flower': ['carnations', 'lilies', 'daffodils'],
        'HairColor': ['black', 'brown', 'blonde'],
        'FavoriteSport': ['soccer', 'basketball', 'tennis'],
        'HouseStyle': ['colonial', 'ranch', 'victorian'],
        'Pet': ['fish', 'dog', 'cat']
    }
    
    perms = {}
    for key, values in attributes.items():
        perms[key] = list(itertools.permutations(values))
    
    solution_found = None
    for name_p in perms['Name']:
        for flower_p in perms['Flower']:
            for hair_p in perms['HairColor']:
                for sport_p in perms['FavoriteSport']:
                    for style_p in perms['HouseStyle']:
                        for pet_p in perms['Pet']:
                            houses = [
                                {
                                    'Name': name_p[0],
                                    'Flower': flower_p[0],
                                    'HairColor': hair_p[0],
                                    'FavoriteSport': sport_p[0],
                                    'HouseStyle': style_p[0],
                                    'Pet': pet_p[0]
                                },
                                {
                                    'Name': name_p[1],
                                    'Flower': flower_p[1],
                                    'HairColor': hair_p[1],
                                    'FavoriteSport': sport_p[1],
                                    'HouseStyle': style_p[1],
                                    'Pet': pet_p[1]
                                },
                                {
                                    'Name': name_p[2],
                                    'Flower': flower_p[2],
                                    'HairColor': hair_p[2],
                                    'FavoriteSport': sport_p[2],
                                    'HouseStyle': style_p[2],
                                    'Pet': pet_p[2]
                                }
                            ]
                            
                            if houses[1]['HairColor'] != 'blonde':
                                continue
                            if houses[1]['Flower'] != 'daffodils':
                                continue
                            if houses[0]['Flower'] != 'carnations':
                                continue
                            if houses[2]['FavoriteSport'] != 'soccer':
                                continue
                            if houses[2]['HouseStyle'] != 'colonial':
                                continue
                            if houses[2]['Pet'] != 'cat':
                                continue
                            
                            peter_house = None
                            for house in houses:
                                if house['Name'] == 'Peter':
                                    peter_house = house
                                    break
                            if peter_house is None or peter_house['FavoriteSport'] != 'basketball':
                                continue
                            if peter_house['Pet'] != 'dog':
                                continue
                            
                            arnold_index = None
                            ranch_index = None
                            for i, house in enumerate(houses):
                                if house['Name'] == 'Arnold':
                                    arnold_index = i
                                if house['HouseStyle'] == 'ranch':
                                    ranch_index = i
                            if arnold_index is None or ranch_index is None or arnold_index + 1 != ranch_index:
                                continue
                            
                            arnold_index = None
                            black_hair_index = None
                            for i, house in enumerate(houses):
                                if house['Name'] == 'Arnold':
                                    arnold_index = i
                                if house['HairColor'] == 'black':
                                    black_hair_index = i
                            if arnold_index is None or black_hair_index is None or arnold_index >= black_hair_index:
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
        header = ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"]
        rows = []
        for i, house in enumerate(solution_found, start=1):
            row = [str(i), house['Name'], house['Flower'], house['HairColor'], house['FavoriteSport'], house['HouseStyle'], house['Pet']]
            rows.append(row)
        
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('{"solution": {}}')

if __name__ == "__main__":
    main()