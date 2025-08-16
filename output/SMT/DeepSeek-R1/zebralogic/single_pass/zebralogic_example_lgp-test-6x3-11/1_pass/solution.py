from z3 import *

def main():
    # Define the attribute values
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hairs = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    # Create enumeration sorts for each attribute
    NameSort, name_consts = EnumSort('Name', names)
    HairSort, hair_consts = EnumSort('Hair', hairs)
    HeightSort, height_consts = EnumSort('Height', heights)
    
    # Create mappings from Z3 constants to string values
    name_map = {name_consts[i]: names[i] for i in range(len(names))}
    hair_map = {hair_consts[i]: hairs[i] for i in range(len(hairs))}
    height_map = {height_consts[i]: heights[i] for i in range(len(heights))}
    
    # Create attribute variables for each house (0-based index: house0 to house5)
    n = 6
    name_vars = [Const('name_%d' % i, NameSort) for i in range(n)]
    hair_vars = [Const('hair_%d' % i, HairSort) for i in range(n)]
    height_vars = [Const('height_%d' % i, HeightSort) for i in range(n)]
    
    s = Solver()
    
    # All names, hairs, and heights are distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(hair_vars))
    s.add(Distinct(height_vars))
    
    # Clue 1: The person who has blonde hair is directly left of Bob.
    # Clue 8: The person who has blonde hair is Carol.
    # So Carol is directly left of Bob.
    s.add(Or([And(name_vars[i] == name_consts[5], name_vars[i+1] == name_consts[0]) for i in range(0, n-1)]))
    
    # Clue 2: Alice is in the fourth house (index 3)
    s.add(name_vars[3] == name_consts[3])  # Alice is at index 3 in names
    
    # Clue 3: The person who is short is Arnold.
    # short is heights[5], Arnold is names[4]
    for i in range(n):
        s.add( (height_vars[i] == height_consts[5]) == (name_vars[i] == name_consts[4]) )
    
    # Clue 4: The person who is tall is in the sixth house (index 5)
    s.add(height_vars[5] == height_consts[3])  # tall is at index 3 in heights
    
    # Clue 5: The person who has black hair is not in the fourth house (index 3)
    s.add(hair_vars[3] != hair_consts[3])  # black is at index 3 in hairs
    
    # Clue 6: The person who has red hair is Eric.
    # red hair is hairs[4], Eric is names[2]
    for i in range(n):
        s.add( (hair_vars[i] == hair_consts[4]) == (name_vars[i] == name_consts[2]) )
    
    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    # super tall: heights[4], average: heights[1]
    # We'll use two integer variables to represent the indices
    avg_idx = Int('avg_idx')
    super_idx = Int('super_idx')
    s.add(avg_idx >= 0, avg_idx < n, super_idx >=0, super_idx < n)
    s.add(If(avg_idx == 0, height_vars[0] == height_consts[1], True))
    s.add(If(avg_idx == 1, height_vars[1] == height_consts[1], True))
    s.add(If(avg_idx == 2, height_vars[2] == height_consts[1], True))
    s.add(If(avg_idx == 3, height_vars[3] == height_consts[1], True))
    s.add(If(avg_idx == 4, height_vars[4] == height_consts[1], True))
    s.add(If(avg_idx == 5, height_vars[5] == height_consts[1], True))
    s.add(If(super_idx == 0, height_vars[0] == height_consts[4], True))
    s.add(If(super_idx == 1, height_vars[1] == height_consts[4], True))
    s.add(If(super_idx == 2, height_vars[2] == height_consts[4], True))
    s.add(If(super_idx == 3, height_vars[3] == height_consts[4], True))
    s.add(If(super_idx == 4, height_vars[4] == height_consts[4], True))
    s.add(If(super_idx == 5, height_vars[5] == height_consts[4], True))
    s.add(super_idx > avg_idx)
    
    # Clue 8: Already used in Clue 1.
    # We have already: blonde hair is Carol -> 
    for i in range(n):
        s.add( (hair_vars[i] == hair_consts[1]) == (name_vars[i] == name_consts[5]) )
    
    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    # Clue 12: The person who has gray hair is in the third house (index 2)
    s.add(hair_vars[2] == hair_consts[5])  # gray hair at house3 (index2)
    # So red hair must be at house1 (index0) or house5 (index4) because |2-0|=2 and |2-4|=2.
    s.add(Or(hair_vars[0] == hair_consts[4], hair_vars[4] == hair_consts[4]))
    
    # Clue 10: The person who is very short is in the fifth house (index4)
    s.add(height_vars[4] == height_consts[2])  # very short is at index2 in heights
    
    # Clue 11: Bob is the person who has brown hair.
    # Bob is names[0], brown hair is hairs[2]
    for i in range(n):
        s.add( (name_vars[i] == name_consts[0]) == (hair_vars[i] == hair_consts[2]) )
    
    # Clue 12: Already set above.
    
    # Clue 13: The person who has blonde hair is the person who is very tall.
    # blonde hair: hair_consts[1], very tall: height_consts[0]
    for i in range(n):
        s.add( (hair_vars[i] == hair_consts[1]) == (height_vars[i] == height_consts[0]) )
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        solution_rows = []
        for i in range(n):
            house_num = str(i+1)
            name_val = model.evaluate(name_vars[i])
            hair_val = model.evaluate(hair_vars[i])
            height_val = model.evaluate(height_vars[i])
            name_str = name_map[name_val]
            hair_str = hair_map[hair_val]
            height_str = height_map[height_val]
            solution_rows.append([house_num, name_str, hair_str, height_str])
        
        # Prepare the output in the required JSON format
        output = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": solution_rows
            }
        }
        import json
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()