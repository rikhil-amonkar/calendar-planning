import itertools
import json

def main():
    attributes = {
        'name': ['Eric', 'Peter', 'Arnold'],
        'drink': ['tea', 'water', 'milk'],
        'nationality': ['dane', 'brit', 'swede'],
        'education': ['high school', 'associate', 'bachelor'],
        'house_style': ['victorian', 'colonial', 'ranch'],
        'smoothie': ['cherry', 'watermelon', 'desert']
    }
    
    perms = {}
    for key in attributes:
        perms[key] = list(itertools.permutations(attributes[key]))
    
    found = False
    solution_rows = None
    
    for name_perm in perms['name']:
        for drink_perm in perms['drink']:
            for nation_perm in perms['nationality']:
                for edu_perm in perms['education']:
                    if edu_perm[1] != 'bachelor':
                        continue
                    for style_perm in perms['house_style']:
                        if style_perm[0] == 'victorian':
                            continue
                        for smooth_perm in perms['smoothie']:
                            assignment = {
                                'name': name_perm,
                                'drink': drink_perm,
                                'nationality': nation_perm,
                                'education': edu_perm,
                                'house_style': style_perm,
                                'smoothie': smooth_perm
                            }
                            
                            # Constraint 1: One house between Eric and tea drinker.
                            eric_index = name_perm.index('Eric')
                            tea_index = drink_perm.index('tea')
                            if abs(eric_index - tea_index) != 2:
                                continue
                            
                            # Constraint 2: Milk drinker is in ranch-style house.
                            milk_index = drink_perm.index('milk')
                            ranch_index = style_perm.index('ranch')
                            if milk_index != ranch_index:
                                continue
                            
                            # Constraint 4: High school diploma holder is Dane.
                            hs_index = edu_perm.index('high school')
                            dane_index = nation_perm.index('dane')
                            if hs_index != dane_index:
                                continue
                            
                            # Constraint 5: Desert smoothie lover is Swede.
                            desert_index = smooth_perm.index('desert')
                            swede_index = nation_perm.index('swede')
                            if desert_index != swede_index:
                                continue
                            
                            # Constraint 7: Cherry smoothie lover is in colonial-style house.
                            cherry_index = smooth_perm.index('cherry')
                            colonial_index = style_perm.index('colonial')
                            if cherry_index != colonial_index:
                                continue
                            
                            # Constraint 8: Arnold is to the right of Victorian house.
                            victorian_index = style_perm.index('victorian')
                            arnold_index = name_perm.index('Arnold')
                            if arnold_index <= victorian_index:
                                continue
                            
                            # Constraint 9: Ranch-style house has high school diploma.
                            if ranch_index != hs_index:
                                continue
                            
                            # All constraints passed.
                            found = True
                            solution_rows = []
                            for i in range(3):
                                row = [
                                    str(i+1),
                                    name_perm[i],
                                    drink_perm[i],
                                    nation_perm[i],
                                    edu_perm[i],
                                    style_perm[i],
                                    smooth_perm[i]
                                ]
                                solution_rows.append(row)
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
    
    if not found:
        solution_rows = []
    
    sol_dict = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": solution_rows
        }
    }
    print(json.dumps(sol_dict))

if __name__ == "__main__":
    main()