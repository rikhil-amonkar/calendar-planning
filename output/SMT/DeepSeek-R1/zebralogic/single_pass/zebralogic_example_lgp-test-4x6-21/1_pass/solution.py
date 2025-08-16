from z3 import *

def main():
    # Define the attribute mappings to integers
    name_dict = {'Peter': 0, 'Arnold': 1, 'Alice': 2, 'Eric': 3}
    flower_dict = {'roses': 0, 'daffodils': 1, 'carnations': 2, 'lilies': 3}  # Note: 'lilies' is used in the problem, but clue says 'lilies'
    hobby_dict = {'photography': 0, 'painting': 1, 'cooking': 2, 'gardening': 3}
    pet_dict = {'dog': 0, 'fish': 1, 'bird': 2, 'cat': 3}
    color_dict = {'red': 0, 'yellow': 1, 'green': 2, 'white': 3}
    style_dict = {'craftsman': 0, 'colonial': 1, 'ranch': 2, 'victorian': 3}
    
    # Reverse mappings for output
    rev_name = {v: k for k, v in name_dict.items()}
    rev_flower = {v: k for k, v in flower_dict.items()}
    rev_hobby = {v: k for k, v in hobby_dict.items()}
    rev_pet = {v: k for k, v in pet_dict.items()}
    rev_color = {v: k for k, v in color_dict.items()}
    rev_style = {v: k for k, v in style_dict.items()}
    
    # Create Z3 variables for each attribute for each house (4 houses, 0-indexed: house0=1, house1=2, etc.)
    n = [Int('n_%i' % i) for i in range(4)]  # names
    f = [Int('f_%i' % i) for i in range(4)]  # flowers
    h = [Int('h_%i' % i) for i in range(4)]  # hobbies
    p = [Int('p_%i' % i) for i in range(4)]  # pets
    c = [Int('c_%i' % i) for i in range(4)]  # colors
    s = [Int('s_%i' % i) for i in range(4)]  # styles
    
    s = Solver()
    
    # Each attribute must be between 0 and 3
    for i in range(4):
        s.add(And(n[i] >= 0, n[i] <= 3))
        s.add(And(f[i] >= 0, f[i] <= 3))
        s.add(And(h[i] >= 0, h[i] <= 3))
        s.add(And(p[i] >= 0, p[i] <= 3))
        s.add(And(c[i] >= 0, c[i] <= 3))
        s.add(And(s[i] >= 0, s[i] <= 3))
    
    # Each attribute list must have distinct values
    s.add(Distinct(n))
    s.add(Distinct(f))
    s.add(Distinct(h))
    s.add(Distinct(p))
    s.add(Distinct(c))
    s.add(Distinct(s))
    
    # Clue 1: The person in a Craftsman-style house is Arnold.
    # Clue 6: The person in a Craftsman-style house is in the second house.
    # So house index1 (which is house2) has style craftsman and name Arnold.
    s.add(s[1] == style_dict['craftsman'])
    s.add(n[1] == name_dict['Arnold'])
    
    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    # Find Peter's house and the rose house, then rose house index > Peter's index.
    peter_house = Int('peter_house')
    rose_house = Int('rose_house')
    s.add(0 <= peter_house, peter_house <= 3)
    s.add(0 <= rose_house, rose_house <= 3)
    s.add(Or([And(peter_house == i, n[i] == name_dict['Peter']) for i in range(4)]))
    s.add(Or([And(rose_house == i, f[i] == flower_dict['roses']) for i in range(4)]))
    s.add(rose_house > peter_house)
    
    # Clue 3: The photography enthusiast is the person who owns a dog.
    for i in range(4):
        s.add(Implies(h[i] == hobby_dict['photography'], p[i] == pet_dict['dog']))
        s.add(Implies(p[i] == pet_dict['dog'], h[i] == hobby_dict['photography']))
    
    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house (index3).
    s.add(f[3] != flower_dict['daffodils'])
    
    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    for i in range(4):
        s.add(Implies(f[i] == flower_dict['roses'], c[i] == color_dict['red']))
        s.add(Implies(c[i] == color_dict['red'], f[i] == flower_dict['roses']))
    
    # Clue 7: Eric is the person residing in a Victorian house.
    for i in range(4):
        s.add(Implies(s[i] == style_dict['victorian'], n[i] == name_dict['Eric']))
        s.add(Implies(n[i] == name_dict['Eric'], s[i] == style_dict['victorian']))
    
    # Clue 8: The person with an aquarium of fish is the person who loves white.
    for i in range(4):
        s.add(Implies(p[i] == pet_dict['fish'], c[i] == color_dict['white']))
        s.add(Implies(c[i] == color_dict['white'], p[i] == pet_dict['fish']))
    
    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    red_house = Int('red_house')
    cook_house = Int('cook_house')
    s.add(0 <= red_house, red_house <= 3)
    s.add(0 <= cook_house, cook_house <= 3)
    s.add(Or([And(red_house == i, c[i] == color_dict['red']) for i in range(4)]))
    s.add(Or([And(cook_house == i, h[i] == hobby_dict['cooking']) for i in range(4)]))
    s.add(cook_house > red_house)
    
    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    for i in range(4):
        s.add(Implies(c[i] == color_dict['white'], f[i] == flower_dict['carnations']))
        s.add(Implies(f[i] == flower_dict['carnations'], c[i] == color_dict['white']))
    
    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    white_house = Int('white_house')
    garden_house = Int('garden_house')
    s.add(0 <= white_house, white_house <= 3)
    s.add(0 <= garden_house, garden_house <= 3)
    s.add(Or([And(white_house == i, c[i] == color_dict['white']) for i in range(4)]))
    s.add(Or([And(garden_house == i, h[i] == hobby_dict['gardening']) for i in range(4)]))
    s.add(white_house > garden_house)
    
    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    for i in range(4):
        s.add(Implies(f[i] == flower_dict['daffodils'], c[i] == color_dict['yellow']))
        s.add(Implies(c[i] == color_dict['yellow'], f[i] == flower_dict['daffodils']))
    
    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    for i in range(4):
        s.add(Implies(s[i] == style_dict['colonial'], c[i] == color_dict['red']))
        s.add(Implies(c[i] == color_dict['red'], s[i] == style_dict['colonial']))
    
    # Clue 14: The person who has a cat is Eric.
    for i in range(4):
        s.add(Implies(p[i] == pet_dict['cat'], n[i] == name_dict['Eric']))
        s.add(Implies(n[i] == name_dict['Eric'], p[i] == pet_dict['cat']))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        # Extract values
        names = [model.evaluate(n[i]).as_long() for i in range(4)]
        flowers = [model.evaluate(f[i]).as_long() for i in range(4)]
        hobbies = [model.evaluate(h[i]).as_long() for i in range(4)]
        pets = [model.evaluate(p[i]).as_long() for i in range(4)]
        colors = [model.evaluate(c[i]).as_long() for i in range(4)]
        styles = [model.evaluate(s[i]).as_long() for i in range(4)]
        
        # Convert to string representation
        soln = []
        for i in range(4):
            house = str(i+1)
            name = rev_name[names[i]]
            flower = rev_flower[flowers[i]]
            hobby = rev_hobby[hobbies[i]]
            pet = rev_pet[pets[i]]
            color = rev_color[colors[i]]
            style = rev_style[styles[i]]
            soln.append([house, name, flower, hobby, pet, color, style])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                "rows": soln
            }
        }
        import json
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()