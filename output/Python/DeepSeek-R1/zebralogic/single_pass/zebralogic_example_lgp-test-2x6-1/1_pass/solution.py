import itertools
import json

def main():
    names = ['Arnold', 'Eric']
    sports = ['basketball', 'soccer']
    hairs = ['brown', 'black']
    heights = ['very short', 'short']
    smoothies = ['desert', 'cherry']
    flowers = ['daffodils', 'carnations']
    
    all_attrs = [names, sports, hairs, heights, smoothies, flowers]
    perms_list = [list(itertools.permutations(attr)) for attr in all_attrs]
    total_assignments = itertools.product(*perms_list)
    
    solution_found = None
    
    for assign in total_assignments:
        name_perm, sport_perm, hair_perm, height_perm, smoothie_perm, flower_perm = assign
        
        house1 = {
            'House': '1',
            'Name': name_perm[0],
            'FavoriteSport': sport_perm[0],
            'HairColor': hair_perm[0],
            'Height': height_perm[0],
            'Smoothie': smoothie_perm[0],
            'Flower': flower_perm[0]
        }
        house2 = {
            'House': '2',
            'Name': name_perm[1],
            'FavoriteSport': sport_perm[1],
            'HairColor': hair_perm[1],
            'Height': height_perm[1],
            'Smoothie': smoothie_perm[1],
            'Flower': flower_perm[1]
        }
        
        # Clue 1: Soccer lover not in second house
        c1 = (house2['FavoriteSport'] != 'soccer')
        
        # Clue 2: Desert smoothie lover directly left of very short
        c2 = (house1['Smoothie'] == 'desert') and (house2['Height'] == 'very short')
        
        # Clue 3: Very short person has brown hair
        c3 = True
        if house1['Height'] == 'very short':
            if house1['HairColor'] != 'brown':
                c3 = False
        if house2['Height'] == 'very short':
            if house2['HairColor'] != 'brown':
                c3 = False
        
        # Clue 4: Carnations lover is Desert smoothie lover
        desert_house = None
        if house1['Smoothie'] == 'desert':
            desert_house = house1
        elif house2['Smoothie'] == 'desert':
            desert_house = house2
            
        carnations_house = None
        if house1['Flower'] == 'carnations':
            carnations_house = house1
        elif house2['Flower'] == 'carnations':
            carnations_house = house2
            
        c4 = (desert_house is not None and carnations_house is not None and desert_house['House'] == carnations_house['House'])
        
        # Clue 5: Eric and brown hair person are next to each other
        eric_house = None
        if house1['Name'] == 'Eric':
            eric_house = house1
        elif house2['Name'] == 'Eric':
            eric_house = house2
            
        brown_hair_house = None
        if house1['HairColor'] == 'brown':
            brown_hair_house = house1
        elif house2['HairColor'] == 'brown':
            brown_hair_house = house2
            
        c5 = False
        if eric_house is not None and brown_hair_house is not None:
            if eric_house != brown_hair_house:
                c5 = True
        
        if c1 and c2 and c3 and c4 and c5:
            solution_found = [house1, house2]
            break
    
    rows = []
    if solution_found:
        for house in solution_found:
            rows.append([
                house['House'],
                house['Name'],
                house['FavoriteSport'],
                house['HairColor'],
                house['Height'],
                house['Smoothie'],
                house['Flower']
            ])
    
    result = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()