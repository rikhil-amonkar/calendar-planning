from z3 import *

def main():
    s = Solver()

    # Attributes mapping to indices
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    musics = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Create Z3 variables for each attribute for 6 houses (index 0 to 5)
    n = [Int('name_%d' % i) for i in range(6)]
    hsty = [Int('style_%d' % i) for i in range(6)]
    msc = [Int('music_%d' % i) for i in range(6)]
    hby = [Int('hobby_%d' % i) for i in range(6)]

    # Each attribute must be in [0,5]
    for i in range(6):
        s.add(n[i] >= 0, n[i] < 6)
        s.add(hsty[i] >= 0, hsty[i] < 6)
        s.add(msc[i] >= 0, msc[i] < 6)
        s.add(hby[i] >= 0, hby[i] < 6)

    # Distinct constraints for each attribute
    s.add(Distinct(n))
    s.add(Distinct(hsty))
    s.add(Distinct(msc))
    s.add(Distinct(hby))

    # Clue 1: Rock music in fifth house (index 4)
    s.add(msc[4] == 5)

    # Clue 2: Classical music (4) and woodworking (3) are adjacent
    s.add(Or([Or(And(msc[i]==4, hby[i+1]==3), And(hby[i]==3, msc[i+1]==4)) for i in range(5)))

    # Clue 3: Mediterranean style (0) and hip hop music (1) at same house
    # Clue 7: Carol (3) is hip hop (1) -> so Carol is in Mediterranean
    for i in range(6):
        s.add(Implies(hsty[i] == 0, msc[i] == 1))
        s.add(Implies(msc[i] == 1, hsty[i] == 0))
        s.add(Implies(n[i] == 3, msc[i] == 1))
        s.add(Implies(msc[i] == 1, n[i] == 3))

    # Clue 4: Arnold (2) and Victorian (5) have |i-j| = 3
    s.add(Or(
        Or([And(n[i] == 2, hsty[i+3] == 5) for i in [0,1,2]]),
        Or([And(n[i] == 2, hsty[i-3] == 5) for i in [3,4,5]])
    ))

    # Clue 5: Jazz (3) is directly left of Eric (0)
    s.add(Or([And(msc[i] == 3, n[i+1] == 0) for i in range(5)]))

    # Clue 6: Hip hop (1) is left of knitting (5)
    s.add(Or([And(msc[i] == 1, hby[j] == 5, i < j) for i in range(6) for j in range(6)]))

    # Clue 8: Craftsman (2) is Arnold (2)
    for i in range(6):
        s.add(Implies(hsty[i] == 2, n[i] == 2))
        s.add(Implies(n[i] == 2, hsty[i] == 2))

    # Clue 9: Ranch (3) is Eric (0)
    # Clue 14: Eric (0) has gardening (4)
    for i in range(6):
        s.add(Implies(hsty[i] == 3, n[i] == 0))
        s.add(Implies(n[i] == 0, hsty[i] == 3))
        s.add(Implies(n[i] == 0, hby[i] == 4))
        s.add(Implies(hby[i] == 4, n[i] == 0))

    # Clue 10: Woodworking (3) is in Victorian (5)
    for i in range(6):
        s.add(Implies(hby[i] == 3, hsty[i] == 5))
        s.add(Implies(hsty[i] == 5, hby[i] == 3))

    # Clue 11: Country music (0) in first house (index0)
    s.add(msc[0] == 0)

    # Clue 12: Painting (1) and colonial (4) have one house between
    s.add(Or(
        [And(hby[i] == 1, hsty[i+2] == 4) for i in range(4)] +
        [And(hby[i] == 1, hsty[i-2] == 4) for i in range(2,6)]
    ))

    # Clue 13: Alice (1) is photography (2)
    for i in range(6):
        s.add(Implies(n[i] == 1, hby[i] == 2))
        s.add(Implies(hby[i] == 2, n[i] == 1))

    # Clue 15: Bob (5) is in third house (index2)
    s.add(n[2] == 5)

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        # Extract values for each house
        solution = []
        for i in range(6):
            ni = model.eval(n[i]).as_long()
            hstyi = model.eval(hsty[i]).as_long()
            msci = model.eval(msc[i]).as_long()
            hbyi = model.eval(hby[i]).as_long()
            solution.append({
                'House': str(i+1),
                'Name': names[ni],
                'HouseStyle': styles[hstyi],
                'MusicGenre': musics[msci],
                'Hobby': hobbies[hbyi]
            })
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": []
            }
        }
        for i in range(6):
            row = solution[i]
            output["solution"]["rows"].append([
                row['House'],
                row['Name'],
                row['HouseStyle'],
                row['MusicGenre'],
                row['Hobby']
            ])
        
        # Print the JSON
        import json
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()