from z3 import *

def main():
    # Define the enums for each attribute
    Name = Enum('Name', ['Peter', 'Eric', 'Alice', 'Arnold'])
    Peter, Eric, Alice, Arnold = Name.__getnewargs__()[1]
    
    Education = Enum('Education', ['bachelor', 'high school', 'associate', 'master'])
    bachelor, high_school, associate, master = Education.__getnewargs__()[1]
    
    MusicGenre = Enum('MusicGenre', ['jazz', 'rock', 'pop', 'classical'])
    jazz, rock, pop, classical = MusicGenre.__getnewargs__()[1]
    
    Color = Enum('Color', ['green', 'red', 'yellow', 'white'])
    green, red, yellow, white = Color.__getnewargs__()[1]
    
    Flower = Enum('Flower', ['lilies', 'carnations', 'daffodils', 'roses'])
    lilies, carnations, daffodils, roses = Flower.__getnewargs__()[1]
    
    # Create variables for each house (0-indexed: house1=0, house2=1, etc.)
    n = [Const(f'n_{i}', Name) for i in range(4)]
    e = [Const(f'e_{i}', Education) for i in range(4)]
    m = [Const(f'm_{i}', MusicGenre) for i in range(4)]
    c = [Const(f'c_{i}', Color) for i in range(4)]
    f = [Const(f'f_{i}', Flower) for i in range(4)]
    
    s = Solver()
    
    # Distinct constraints for each attribute
    s.add(Distinct(n))
    s.add(Distinct(e))
    s.add(Distinct(m))
    s.add(Distinct(c))
    s.add(Distinct(f))
    
    # Clue 1: bachelor <-> daffodils
    for i in range(4):
        s.add( (e[i] == bachelor) == (f[i] == daffodils) )
    
    # Clue 2: carnations not in first house (house0)
    s.add(f[0] != carnations)
    
    # Clue 3: master's degree is Alice
    for i in range(4):
        s.add( (e[i] == master) == (n[i] == Alice) )
    
    # Clue 4: master's degree directly left of classical music
    s.add(Or(
        And(e[0] == master, m[1] == classical),
        And(e[1] == master, m[2] == classical),
        And(e[2] == master, m[3] == classical)
    ))
    
    # Clue 5: Eric not in second house (house1)
    s.add(n[1] != Eric)
    
    # Clue 6: Arnold not in third house (house2)
    s.add(n[2] != Arnold)
    
    # Clue 7: yellow directly left of roses
    s.add(Or(
        And(c[0] == yellow, f[1] == roses),
        And(c[1] == yellow, f[2] == roses),
        And(c[2] == yellow, f[3] == roses)
    ))
    
    # Clue 8: pop music in second house (house1)
    s.add(m[1] == pop)
    
    # Clue 9: associate not in fourth house (house3)
    s.add(e[3] != associate)
    
    # Clue 10: carnations not in fourth house (house3)
    s.add(f[3] != carnations)
    
    # Clue 11: red directly left of white
    s.add(Or(
        And(c[0] == red, c[1] == white),
        And(c[1] == red, c[2] == white),
        And(c[2] == red, c[3] == white)
    ))
    
    # Clue 12: red <-> rock
    for i in range(4):
        s.add( (c[i] == red) == (m[i] == rock) )
    
    # Clue 13: Arnold loves yellow
    for i in range(4):
        s.add(Implies(n[i] == Arnold, c[i] == yellow))
    
    # Clue 14: daffodils <-> yellow
    for i in range(4):
        s.add( (f[i] == daffodils) == (c[i] == yellow) )
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        solution = []
        for i in range(4):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            edu_val = model.eval(e[i])
            music_val = model.eval(m[i])
            color_val = model.eval(c[i])
            flower_val = model.eval(f[i])
            row = [house_num, 
                   str(name_val), 
                   str(edu_val), 
                   str(music_val), 
                   str(color_val), 
                   str(flower_val)]
            solution.append(row)
        
        # Format as JSON
        json_output = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": solution
            }
        }
        import json
        print(json.dumps(json_output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()