import json

def check_constraints(assignment):
    house1 = assignment[0]
    house2 = assignment[1]
    
    # Clue 1: The Desert smoothie lover is Arnold.
    for house in assignment:
        name = house[0]
        smoothie = house[3]
        if name == 'Arnold':
            if smoothie != 'desert':
                return False
        if smoothie == 'desert':
            if name != 'Arnold':
                return False
                
    # Clue 2: The person who has brown hair is the person who loves basketball.
    for house in assignment:
        hair = house[1]
        sport = house[2]
        if hair == 'brown':
            if sport != 'basketball':
                return False
        if sport == 'basketball':
            if hair != 'brown':
                return False
                
    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    # Determine house numbers for Arnold and black hair.
    if house1[0] == 'Arnold':
        arnold_house = 1
    else:
        arnold_house = 2
        
    if house1[1] == 'black':
        black_hair_house = 1
    else:
        black_hair_house = 2
        
    if arnold_house >= black_hair_house:
        return False
        
    return True

def main():
    names = [('Arnold', 'Eric'), ('Eric', 'Arnold')]
    hairs = [('black', 'brown'), ('brown', 'black')]
    sports = [('basketball', 'soccer'), ('soccer', 'basketball')]
    smoothies = [('desert', 'cherry'), ('cherry', 'desert')]
    
    found_solution = False
    solution_assignment = None
    
    for n in names:
        for h in hairs:
            for s in sports:
                for sm in smoothies:
                    assignment = [
                        [n[0], h[0], s[0], sm[0]],
                        [n[1], h[1], s[1], sm[1]]
                    ]
                    if check_constraints(assignment):
                        found_solution = True
                        solution_assignment = assignment
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break
            
    if solution_assignment is None:
        solution_assignment = [
            ["Unknown", "Unknown", "Unknown", "Unknown"],
            ["Unknown", "Unknown", "Unknown", "Unknown"]
        ]
    
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": [
                ["1"] + solution_assignment[0],
                ["2"] + solution_assignment[1]
            ]
        }
    }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()