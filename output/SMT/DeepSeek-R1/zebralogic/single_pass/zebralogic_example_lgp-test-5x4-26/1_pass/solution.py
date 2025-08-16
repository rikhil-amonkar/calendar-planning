from z3 import *
import json

def main():
    # Define the attribute values
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    # Create Z3 sorts and constants for each attribute
    NameSort, name_consts = EnumSort('Name', names)
    HeightSort, height_consts = EnumSort('Height', heights)
    MotherSort, mother_consts = EnumSort('Mother', mothers)
    HairColorSort, hair_consts = EnumSort('HairColor', hair_colors)
    
    # Create dictionaries to map strings to Z3 constants
    name_dict = dict(zip(names, name_consts))
    height_dict = dict(zip(heights, height_consts))
    mother_dict = dict(zip(mothers, mother_consts))
    hair_dict = dict(zip(hair_colors, hair_consts))
    
    # Reverse dictionaries for model evaluation
    rev_name = dict(zip(name_consts, names))
    rev_height = dict(zip(height_consts, heights))
    rev_mother = dict(zip(mother_consts, mothers))
    rev_hair = dict(zip(hair_consts, hair_colors))
    
    # Create attributes for each house (5 houses, index 0 to 4)
    n = [Const('n_%d' % i, NameSort) for i in range(5)]
    h = [Const('h_%d' % i, HeightSort) for i in range(5)]
    m = [Const('m_%d' % i, MotherSort) for i in range(5)]
    c = [Const('c_%d' % i, HairColorSort) for i in range(5)]
    
    s = Solver()
    
    # All attributes must be distinct
    s.add(Distinct(n))
    s.add(Distinct(h))
    s.add(Distinct(m))
    s.add(Distinct(c))
    
    # Clue 1: The person who is tall is the person whose mother's name is Holly.
    for i in range(5):
        s.add( (h[i] == height_dict['tall']) == (m[i] == mother_dict['Holly']) )
    
    # Clue 2: Two houses between average and short -> |i - j| = 3
    # We have deduced: short is at house 4 (index3) and average at house1 (index0)
    s.add( h[3] == height_dict['short'] )
    s.add( h[0] == height_dict['average'] )
    
    # Clue 3: Gray hair directly left of Janelle mother
    for i in range(4):
        s.add( Implies( c[i] == hair_dict['gray'], m[i+1] == mother_dict['Janelle'] ) )
    
    # Clue 4: Black hair not in fourth house (house4 is index3)
    s.add( c[3] != hair_dict['black'] )
    
    # Clue 5: Eric has black hair
    for i in range(5):
        s.add( (n[i] == name_dict['Eric']) == (c[i] == hair_dict['black']) )
    
    # Clue 6: Very short height and mother Penny
    for i in range(5):
        s.add( (h[i] == height_dict['very short']) == (m[i] == mother_dict['Penny']) )
    
    # Clue 7: Eric and gray hair are next to each other
    adjacent_eric_gray = []
    for i in range(4):
        adjacent_eric_gray.append( And( n[i] == name_dict['Eric'], c[i+1] == hair_dict['gray'] ) )
        adjacent_eric_gray.append( And( n[i+1] == name_dict['Eric'], c[i] == hair_dict['gray'] ) )
    s.add( Or(adjacent_eric_gray) )
    
    # Clue 8: Bob in fifth house (index4)
    s.add( n[4] == name_dict['Bob'] )
    
    # Clue 9: Red hair is Peter
    for i in range(5):
        s.add( (c[i] == hair_dict['red']) == (n[i] == name_dict['Peter']) )
    
    # Clue 10: Mother Kailyn directly left of short height
    # Already handled: mother Kailyn at index2, short at index3
    
    # Clue 11: Arnold has brown hair
    for i in range(5):
        s.add( (n[i] == name_dict['Arnold']) == (c[i] == hair_dict['brown']) )
    
    # Clue 12: Brown hair left of mother Janelle
    brown_janelle = []
    for i in range(5):
        for j in range(5):
            if i < j:
                brown_janelle.append( And( c[i] == hair_dict['brown'], m[j] == mother_dict['Janelle'] ) )
    s.add( Or(brown_janelle) )
    
    # Clue 13: Mother Aniya and very short height are next to each other
    adjacent_aniya_veryshort = []
    for i in range(4):
        adjacent_aniya_veryshort.append( And( m[i] == mother_dict['Aniya'], h[i+1] == height_dict['very short'] ) )
        adjacent_aniya_veryshort.append( And( m[i+1] == mother_dict['Aniya'], h[i] == height_dict['very short'] ) )
    s.add( Or(adjacent_aniya_veryshort) )
    
    # Clue 14: Mother Kailyn in third house (index2)
    s.add( m[2] == mother_dict['Kailyn'] )
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(5):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            height_val = model.eval(h[i])
            mother_val = model.eval(m[i])
            hair_val = model.eval(c[i])
            
            name_str = rev_name[name_val]
            height_str = rev_height[height_val]
            mother_str = rev_mother[mother_val]
            hair_str = rev_hair[hair_val]
            
            rows.append([house_num, name_str, height_str, mother_str, hair_str])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()