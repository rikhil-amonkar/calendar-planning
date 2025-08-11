import json

def main():
    names = ['Eric', 'Arnold']
    styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    
    candidates = []
    
    for name1 in names:
        name2 = next(n for n in names if n != name1)
        for style1 in styles:
            style2 = next(s for s in styles if s != style1)
            for smoothie1 in smoothies:
                smoothie2 = next(sm for sm in smoothies if sm != smoothie1)
                for pet1 in pets:
                    pet2 = next(p for p in pets if p != pet1)
                    candidate = {
                        1: [name1, style1, smoothie1, pet1],
                        2: [name2, style2, smoothie2, pet2]
                    }
                    candidates.append(candidate)
    
    solution_found = None
    for cand in candidates:
        house1 = cand[1]
        house2 = cand[2]
        
        valid1 = True
        if house1[2] == 'cherry' and house1[3] != 'dog':
            valid1 = False
        if house2[2] == 'cherry' and house2[3] != 'dog':
            valid1 = False
            
        valid2 = True
        if house1[1] == 'victorian' and house1[3] != 'dog':
            valid2 = False
        if house2[1] == 'victorian' and house2[3] != 'dog':
            valid2 = False
            
        victorian_house = 1 if house1[1] == 'victorian' else 2
        eric_house = 1 if house1[0] == 'Eric' else 2
        valid3 = (victorian_house < eric_house)
        
        if valid1 and valid2 and valid3:
            solution_found = cand
            break
    
    if solution_found is None:
        output = {
            "solution": {
                "header": ["House", "Name", "House Style", "Smoothie", "Pet"],
                "rows": []
            }
        }
    else:
        row1 = ["1"] + solution_found[1]
        row2 = ["2"] + solution_found[2]
        output = {
            "solution": {
                "header": ["House", "Name", "House Style", "Smoothie", "Pet"],
                "rows": [row1, row2]
            }
        }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()