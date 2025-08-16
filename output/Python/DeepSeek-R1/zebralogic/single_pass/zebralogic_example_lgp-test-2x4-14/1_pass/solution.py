import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    
    name_perms = list(itertools.permutations(names))
    style_perms = list(itertools.permutations(styles))
    smoothie_perms = list(itertools.permutations(smoothies))
    pet_perms = list(itertools.permutations(pets))
    
    solution_rows = None
    found = False
    
    for name_perm in name_perms:
        if found:
            break
        for style_perm in style_perms:
            if found:
                break
            for smoothie_perm in smoothie_perms:
                if found:
                    break
                for pet_perm in pet_perms:
                    house0_attrs = [name_perm[0], style_perm[0], smoothie_perm[0], pet_perm[0]]
                    house1_attrs = [name_perm[1], style_perm[1], smoothie_perm[1], pet_perm[1]]
                    
                    c1_0 = (house0_attrs[2] == 'cherry' and house0_attrs[3] == 'dog')
                    c1_1 = (house1_attrs[2] == 'cherry' and house1_attrs[3] == 'dog')
                    if not (c1_0 or c1_1):
                        continue
                    
                    c2_0 = (house0_attrs[1] == 'victorian' and house0_attrs[3] == 'dog')
                    c2_1 = (house1_attrs[1] == 'victorian' and house1_attrs[3] == 'dog')
                    if not (c2_0 or c2_1):
                        continue
                    
                    vic_index = 0 if style_perm[0] == 'victorian' else 1
                    eric_index = 0 if name_perm[0] == 'Eric' else 1
                    
                    if vic_index < eric_index:
                        solution_rows = [
                            ["1", name_perm[0], style_perm[0], smoothie_perm[0], pet_perm[0]],
                            ["2", name_perm[1], style_perm[1], smoothie_perm[1], pet_perm[1]]
                        ]
                        found = True
                        break
    
    if solution_rows is None:
        solution_rows = []
    
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()