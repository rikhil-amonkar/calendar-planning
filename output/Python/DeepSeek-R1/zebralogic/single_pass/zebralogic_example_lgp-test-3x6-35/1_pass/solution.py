import itertools
import json

def main():
    # Define the domains for each attribute
    domains = {
        'Name': ['Eric', 'Arnold', 'Peter'],
        'Vacation': ['mountain', 'city', 'beach'],
        'Height': ['very short', 'average', 'short'],
        'Flower': ['carnations', 'daffodils', 'lilies'],
        'HairColor': ['brown', 'black', 'blonde'],
        'Education': ['associate', 'bachelor', 'high school']
    }
    
    # Pre-filter permutations for attributes with fixed positions
    vac_perms = [p for p in itertools.permutations(domains['Vacation']) if p[0] == 'beach']  # Clue 4
    edu_perms = [p for p in itertools.permutations(domains['Education']) if p[2] == 'high school']  # Clue 5
    hair_perms = [p for p in itertools.permutations(domains['HairColor']) if p[2] == 'blonde']  # Clue 10
    
    # Full permutations for other attributes
    name_perms = list(itertools.permutations(domains['Name']))
    height_perms = list(itertools.permutations(domains['Height']))
    flower_perms = list(itertools.permutations(domains['Flower']))
    
    # Iterate through all combinations of permutations
    for name in name_perms:
        for vac in vac_perms:
            for height in height_perms:
                for flower in flower_perms:
                    for hair in hair_perms:
                        for edu in edu_perms:
                            # Assign the current permutation set to houses
                            assignment = {
                                'Name': name,
                                'Vacation': vac,
                                'Height': height,
                                'Flower': flower,
                                'HairColor': hair,
                                'Education': edu
                            }
                            
                            # Check all clues
                            # Clue 1: Peter has average height
                            peter_index = name.index('Peter')
                            if height[peter_index] != 'average':
                                continue
                            
                            # Clue 2: Daffodils belong to Arnold
                            daffodil_index = flower.index('daffodils')
                            if name[daffodil_index] != 'Arnold':
                                continue
                            
                            # Clue 3: Very short not in second house (index 1)
                            very_short_index = height.index('very short')
                            if very_short_index == 1:
                                continue
                            
                            # Clue 6: Short is to the right of very short
                            short_index = height.index('short')
                            if short_index <= very_short_index:
                                continue
                            
                            # Clue 7: Lilies belong to Eric
                            lilies_index = flower.index('lilies')
                            if name[lilies_index] != 'Eric':
                                continue
                            
                            # Clue 8: Lilies imply bachelor's degree
                            if edu[lilies_index] != 'bachelor':
                                continue
                            
                            # Clue 9: City break is to the right of Peter
                            city_index = vac.index('city')
                            if city_index <= peter_index:
                                continue
                            
                            # Clue 11: Beach vacation (index0) has brown hair
                            if hair[0] != 'brown':
                                continue
                            
                            # All constraints satisfied, build the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                                    "rows": []
                                }
                            }
                            
                            for i in range(3):
                                house = [
                                    str(i+1),
                                    name[i],
                                    vac[i],
                                    height[i],
                                    flower[i],
                                    hair[i],
                                    edu[i]
                                ]
                                solution['solution']['rows'].append(house)
                            
                            # Output the solution as JSON
                            print(json.dumps(solution))
                            return
    
    # If no solution found, output an empty solution structure
    print(json.dumps({"solution": {"header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"], "rows": []}}))

if __name__ == "__main__":
    main()