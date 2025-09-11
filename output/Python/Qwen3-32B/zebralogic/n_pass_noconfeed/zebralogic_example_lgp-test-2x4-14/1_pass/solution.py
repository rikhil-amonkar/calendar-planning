import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    
    for names_perm in itertools.permutations(names):
        for house_styles_perm in itertools.permutations(house_styles):
            for smoothies_perm in itertools.permutations(smoothies):
                for pets_perm in itertools.permutations(pets):
                    # Check constraint 1: Cherry smoothie <-> Dog
                    cherry_house = None
                    for i in [0, 1]:
                        if smoothies_perm[i] == 'cherry':
                            cherry_house = i
                    if pets_perm[cherry_house] != 'dog':
                        continue
                    
                    # Check constraint 2: Victorian house <-> Dog
                    victorian_house = None
                    for i in [0, 1]:
                        if house_styles_perm[i] == 'victorian':
                            victorian_house = i
                    if pets_perm[victorian_house] != 'dog':
                        continue
                    
                    # Check constraint 3: Victorian house is left of Eric
                    eric_house = None
                    for i in [0, 1]:
                        if names_perm[i] == 'Eric':
                            eric_house = i
                    if victorian_house is None or eric_house is None:
                        continue
                    if victorian_house >= eric_house:
                        continue
                    
                    # Build solution
                    rows = []
                    for i in [0, 1]:
                        house_num = str(i + 1)
                        name = names_perm[i]
                        style = house_styles_perm[i]
                        smoothie = smoothies_perm[i]
                        pet = pets_perm[i]
                        rows.append([house_num, name, style, smoothie, pet])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                            "rows": rows
                        }
                    }
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

solution = solve_puzzle()
print(json.dumps(solution, indent=2))