import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]
    houses = [1, 2, 3, 4]
    
    # Generate all permutations for each attribute across 4 houses
    all_names = list(permutations(names, 4))
    all_flowers = list(permutations(flowers, 4))
    all_hobbies = list(permutations(hobbies, 4))
    all_pets = list(permutations(pets, 4))
    all_colors = list(permutations(colors, 4))
    all_styles = list(permutations(house_styles, 4))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_names:
        # Clue 1 & 6: Arnold is in Craftsman house, which is house 2
        if name_perm[1] != "Arnold":  # house 2 is index 1
            continue
            
        for style_perm in all_styles:
            # Clue 6: Craftsman is house 2
            if style_perm[1] != "craftsman":
                continue
            # Clue 1: Arnold is in Craftsman (already enforced by house 2)
            # Clue 7: Eric is in Victorian
            eric_index = name_perm.index("Eric")
            if style_perm[eric_index] != "victorian":
                continue
                
            for color_perm in all_colors:
                # Clue 13: Colonial house has red color
                try:
                    colonial_index = style_perm.index("colonial")
                    if color_perm[colonial_index] != "red":
                        continue
                except ValueError:
                    continue
                    
                for flower_perm in all_flowers:
                    # Clue 4: Daffodils not in house 4
                    if flower_perm[3] == "daffodils":
                        continue
                    # Clue 12: Daffodils = yellow
                    daffodil_index = flower_perm.index("daffodils")
                    if color_perm[daffodil_index] != "yellow":
                        continue
                    # Clue 5: Roses = red
                    rose_index = flower_perm.index("roses")
                    if color_perm[rose_index] != "red":
                        continue
                    # Clue 10: White = carnations
                    white_index = color_perm.index("white")
                    if flower_perm[white_index] != "carnations":
                        continue
                        
                    for pet_perm in all_pets:
                        # Clue 14: Eric has cat
                        if pet_perm[eric_index] != "cat":
                            continue
                        # Clue 8: Fish = white
                        fish_index = pet_perm.index("fish")
                        if color_perm[fish_index] != "white":
                            continue
                            
                        for hobby_perm in all_hobbies:
                            # Clue 3: Photography = dog
                            photo_index = hobby_perm.index("photography")
                            if pet_perm[photo_index] != "dog":
                                continue
                                
                            # Clue 2: Roses is to the right of Peter
                            peter_index = name_perm.index("Peter")
                            if rose_index <= peter_index:
                                continue
                                
                            # Clue 9: Cooking is to the right of red
                            cooking_index = hobby_perm.index("cooking")
                            if cooking_index <= rose_index:  # rose_index = red_index from clue 5
                                continue
                                
                            # Clue 11: White is to the right of gardening
                            gardening_index = hobby_perm.index("gardening")
                            if white_index <= gardening_index:
                                continue
                                
                            # All constraints satisfied, found a solution
                            solution = []
                            for i in range(4):
                                solution.append([
                                    str(i + 1),
                                    name_perm[i],
                                    flower_perm[i],
                                    hobby_perm[i],
                                    pet_perm[i],
                                    color_perm[i],
                                    style_perm[i]
                                ])
                            solutions.append(solution)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution (should be unique)
    solution_rows = solutions[0]
    
    result = {
        "solution": {
            "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
            "rows": solution_rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))