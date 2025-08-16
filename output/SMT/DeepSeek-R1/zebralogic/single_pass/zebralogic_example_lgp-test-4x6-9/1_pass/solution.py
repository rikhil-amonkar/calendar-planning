from z3 import *

def main():
    # Define the mappings from integers to attribute values
    names_map = ['Peter', 'Arnold', 'Eric', 'Alice']
    flowers_map = ['daffodils', 'carnations', 'roses', 'lilies']
    heights_map = ['very short', 'short', 'tall', 'average']
    mothers_map = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
    occupations_map = ['engineer', 'doctor', 'teacher', 'artist']
    sports_map = ['swimming', 'basketball', 'tennis', 'soccer']

    # Create Z3 variables for each attribute for 4 houses (index 0 to 3 for house1 to house4)
    n = [Int('n_%d' % i) for i in range(4)]   # names
    f = [Int('f_%d' % i) for i in range(4)]   # flowers
    h = [Int('h_%d' % i) for i in range(4)]   # heights
    m = [Int('m_%d' % i) for i in range(4)]   # mothers
    o = [Int('o_%d' % i) for i in range(4)]   # occupations
    sp = [Int('sp_%d' % i) for i in range(4)] # sports

    s = Solver()

    # Add distinct constraints for each attribute
    s.add(Distinct(n))
    s.add(Distinct(f))
    s.add(Distinct(h))
    s.add(Distinct(m))
    s.add(Distinct(o))
    s.add(Distinct(sp))

    # Each attribute must be in [0, 3]
    for i in range(4):
        s.add(n[i] >= 0, n[i] <= 3)
        s.add(f[i] >= 0, f[i] <= 3)
        s.add(h[i] >= 0, h[i] <= 3)
        s.add(m[i] >= 0, m[i] <= 3)
        s.add(o[i] >= 0, o[i] <= 3)
        s.add(sp[i] >= 0, sp[i] <= 3)

    # Clue 1: The person who loves swimming is the person who loves the rose bouquet.
    for i in range(4):
        s.add( (sp[i] == 0) == (f[i] == 2) )  # swimming=0, roses=2

    # Clue 2: The person who loves the rose bouquet is Eric.
    for i in range(4):
        s.add( (f[i] == 2) == (n[i] == 2) )   # roses=2, Eric=2

    # Clue 3: Arnold is the person who is tall.
    for i in range(4):
        s.add( (n[i] == 1) == (h[i] == 2) )   # Arnold=1, tall=2

    # Clue 4: The person who loves daffodils is to the right of the engineer.
    engineer_index = Int('engineer_index')
    daffodil_index = Int('daffodil_index')
    s.add(Or([And(o[i] == 0, engineer_index == i) for i in range(4)]))
    s.add(Or([And(f[i] == 0, daffodil_index == i) for i in range(4)]))
    s.add(daffodil_index > engineer_index)

    # Clue 5: The person who loves soccer is the person who is short.
    for i in range(4):
        s.add( (sp[i] == 3) == (h[i] == 1) )  # soccer=3, short=1

    # Clue 6: The person who is a teacher is in the first house.
    s.add(o[0] == 2)  # teacher=2

    # Clue 7: The person whose mother is Janelle loves carnations.
    for i in range(4):
        s.add( (m[i] == 0) == (f[i] == 1) )   # Janelle=0, carnations=1

    # Clue 8: The person who loves basketball has average height.
    for i in range(4):
        s.add( (sp[i] == 1) == (h[i] == 3) )  # basketball=1, average=3

    # Clue 9: Arnold is not in the third house.
    s.add(n[2] != 1)  # third house index=2, Arnold=1

    # Clue 10: The person whose mother is Holly is to the right of the person with average height.
    holly_index = Int('holly_index')
    avg_index = Int('avg_index')
    s.add(Or([And(m[i] == 2, holly_index == i) for i in range(4)]))  # Holly=2
    s.add(Or([And(h[i] == 3, avg_index == i) for i in range(4)]))     # average=3
    s.add(holly_index > avg_index)

    # Clue 11: Peter is a doctor.
    for i in range(4):
        s.add( (n[i] == 0) == (o[i] == 1) )   # Peter=0, doctor=1

    # Clue 12: The person whose mother is Aniya is Alice.
    for i in range(4):
        s.add( (m[i] == 3) == (n[i] == 3) )   # Aniya=3, Alice=3

    # Clue 13: Arnold loves lilies.
    for i in range(4):
        s.add( (n[i] == 1) == (f[i] == 3) )   # Arnold=1, lilies=3

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        solution = []
        for i in range(4):
            ni = model.evaluate(n[i]).as_long()
            fi = model.evaluate(f[i]).as_long()
            hi = model.evaluate(h[i]).as_long()
            mi_val = model.evaluate(m[i]).as_long()
            oi = model.evaluate(o[i]).as_long()
            spi = model.evaluate(sp[i]).as_long()
            row = [
                str(i+1), 
                names_map[ni], 
                flowers_map[fi], 
                heights_map[hi], 
                mothers_map[mi_val], 
                occupations_map[oi], 
                sports_map[spi]
            ]
            solution.append(row)
        
        # Format the solution as JSON
        json_output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": solution
            }
        }
        import json
        print(json.dumps(json_output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()