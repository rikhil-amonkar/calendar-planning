import z3
import json

def main():
    # Define the attributes
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    # Create enums for each category
    Name = z3.EnumSort('Name', names)
    HairColor = z3.EnumSort('HairColor', hair_colors)
    Height = z3.EnumSort('Height', heights)
    
    # Create constants for each value
    name_consts = [z3.Const(name, Name) for name in names]
    hair_consts = [z3.Const(color, HairColor) for color in hair_colors]
    height_consts = [z3.Const(h, Height) for h in heights]
    
    # Create dictionaries for easy lookup
    name_dict = dict(zip(names, name_consts))
    hair_dict = dict(zip(hair_colors, hair_consts))
    height_dict = dict(zip(heights, height_consts))
    
    # Create variables for each house (1-indexed)
    n = [z3.Const(f'n_{i}', Name) for i in range(1, 7)]
    hc = [z3.Const(f'hc_{i}', HairColor) for i in range(1, 7)]
    ht = [z3.Const(f'ht_{i}', Height) for i in range(1, 7)]
    
    s = z3.Solver()
    
    # All attributes are distinct per house
    s.add(z3.Distinct(n))
    s.add(z3.Distinct(hc))
    s.add(z3.Distinct(ht))
    
    # Add clues
    # 1. The person who has blonde hair is directly left of Bob.
    for i in range(1, 6):
        s.add(z3.Implies(hc[i-1] == hair_dict['blonde'], n[i] == name_dict['Bob']))
    
    # 2. Alice is in the fourth house.
    s.add(n[3] == name_dict['Alice'])
    
    # 3. The person who is short is Arnold.
    for i in range(6):
        s.add(z3.Implies(ht[i] == height_dict['short'], n[i] == name_dict['Arnold']))
    
    # 4. The person who is tall is in the sixth house.
    s.add(ht[5] == height_dict['tall'])
    
    # 5. The person who has black hair is not in the fourth house.
    s.add(hc[3] != hair_dict['black'])
    
    # 6. The person who has red hair is Eric.
    for i in range(6):
        s.add(z3.Implies(hc[i] == hair_dict['red'], n[i] == name_dict['Eric']))
    
    # 7. The person who is super tall is somewhere to the right of the person who has an average height.
    avg_index = z3.Int('avg_index')
    super_index = z3.Int('super_index')
    s.add(avg_index >= 0, avg_index < 6)
    s.add(super_index >= 0, super_index < 6)
    for i in range(6):
        s.add(z3.Implies(ht[i] == height_dict['average'], avg_index == i))
        s.add(z3.Implies(ht[i] == height_dict['super tall'], super_index == i))
    s.add(super_index > avg_index)
    
    # 8. The person who has blonde hair is Carol.
    for i in range(6):
        s.add(z3.Implies(hc[i] == hair_dict['blonde'], n[i] == name_dict['Carol']))
    
    # 9. There is one house between the person who has gray hair and the person who has red hair.
    gray_index = z3.Int('gray_index')
    red_index = z3.Int('red_index')
    s.add(gray_index >= 0, gray_index < 6)
    s.add(red_index >= 0, red_index < 6)
    for i in range(6):
        s.add(z3.Implies(hc[i] == hair_dict['gray'], gray_index == i))
        s.add(z3.Implies(hc[i] == hair_dict['red'], red_index == i))
    s.add(z3.Or(
        gray_index == red_index + 2,
        red_index == gray_index + 2
    ))
    
    # 10. The person who is very short is in the fifth house.
    s.add(ht[4] == height_dict['very short'])
    
    # 11. Bob is the person who has brown hair.
    for i in range(6):
        s.add(z3.Implies(n[i] == name_dict['Bob'], hc[i] == hair_dict['brown']))
    
    # 12. The person who has gray hair is in the third house.
    s.add(hc[2] == hair_dict['gray'])
    
    # 13. The person who has blonde hair is the person who is very tall.
    for i in range(6):
        s.add(z3.Implies(hc[i] == hair_dict['blonde'], ht[i] == height_dict['very tall']))
    
    # Check and get the model
    if s.check() == z3.sat:
        model = s.model()
        
        # Extract values
        result = []
        for i in range(6):
            house_num = str(i+1)
            name_val = None
            hair_val = None
            height_val = None
            
            # Find the name value
            for name in names:
                if model.eval(n[i]) == name_dict[name]:
                    name_val = name
                    break
                    
            # Find the hair color value
            for color in hair_colors:
                if model.eval(hc[i]) == hair_dict[color]:
                    hair_val = color
                    break
                    
            # Find the height value
            for h in heights:
                if model.eval(ht[i]) == height_dict[h]:
                    height_val = h
                    break
                    
            result.append([house_num, name_val, hair_val, height_val])
        
        # Format output
        output = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()