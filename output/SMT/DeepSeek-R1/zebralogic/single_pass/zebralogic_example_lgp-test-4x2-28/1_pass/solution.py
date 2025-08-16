import z3
import json

def main():
    # Create variables for names and hairs for four houses
    names = [z3.Int('n0'), z3.Int('n1'), z3.Int('n2'), z3.Int('n3')]
    hairs = [z3.Int('h0'), z3.Int('h1'), z3.Int('h2'), z3.Int('h3')]
    
    s = z3.Solver()
    
    # Each name and hair variable must be between 0 and 3
    for i in range(4):
        s.add(names[i] >= 0, names[i] <= 3)
        s.add(hairs[i] >= 0, hairs[i] <= 3)
    
    # Names are all different
    s.add(z3.Distinct(names[0], names[1], names[2], names[3]))
    # Hairs are all different
    s.add(z3.Distinct(hairs[0], hairs[1], hairs[2], hairs[3]))
    
    # Clue 1: Eric (3) is directly left of the person with blonde hair (1)
    s.add(z3.Or(
        z3.And(names[0] == 3, hairs[1] == 1),
        z3.And(names[1] == 3, hairs[2] == 1),
        z3.And(names[2] == 3, hairs[3] == 1)
    ))
    
    # Clue 2: Alice (0) and Arnold (1) are adjacent
    adjacent = []
    for i in range(3):
        adjacent.append(z3.And(names[i] == 0, names[i+1] == 1))
        adjacent.append(z3.And(names[i] == 1, names[i+1] == 0))
    s.add(z3.Or(adjacent))
    
    # Clue 3: Eric (3) has brown hair (2)
    for i in range(4):
        s.add(z3.Implies(names[i] == 3, hairs[i] == 2))
    
    # Clue 4: Black hair (0) is not in the first house
    s.add(hairs[0] != 0)
    
    # Clue 5: Alice (0) is in the first house
    s.add(names[0] == 0)
    
    if s.check() == z3.sat:
        m = s.model()
        name_map = {0: 'Alice', 1: 'Arnold', 2: 'Peter', 3: 'Eric'}
        hair_map = {0: 'black', 1: 'blonde', 2: 'brown', 3: 'red'}
        
        rows = []
        for i in range(4):
            ni = m[names[i]].as_long()
            hi = m[hairs[i]].as_long()
            house_num = str(i+1)
            name_str = name_map[ni]
            hair_str = hair_map[hi]
            rows.append([house_num, name_str, hair_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()