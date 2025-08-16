from z3 import *
import json

def main():
    s = Solver()
    houses = range(4)  # houses indices: 0->House1, 1->House2, 2->House3, 3->House4

    # Create variables for each attribute for every house.
    name  = [Int(f"name_{i}") for i in houses]   # Name: 0=Arnold, 1=Peter, 2=Eric, 3=Alice
    edu   = [Int(f"edu_{i}") for i in houses]     # Education: 0=bachelor, 1=master, 2=high school, 3=associate
    music = [Int(f"music_{i}") for i in houses]   # MusicGenre: 0=jazz, 1=rock, 2=pop, 3=classical
    color = [Int(f"color_{i}") for i in houses]   # Color: 0=yellow, 1=green, 2=red, 3=white
    flower= [Int(f"flower_{i}") for i in houses]  # Flower: 0=daffodils, 1=carnations, 2=roses, 3=lilies

    # Each variable takes a value from 0 to 3.
    for var_list in [name, edu, music, color, flower]:
        for v in var_list:
            s.add(v >= 0, v < 4)

    # All attributes are unique across houses.
    s.add(Distinct(name))
    s.add(Distinct(edu))
    s.add(Distinct(music))
    s.add(Distinct(color))
    s.add(Distinct(flower))

    # --- Encoding the clues ---

    # Clues (1) and (14):
    # "The person with a bachelor's degree is the person who loves a bouquet of daffodils."
    # "The person who loves a bouquet of daffodils is the person who loves yellow."
    # We encode these as equivalences between edu==bachelor, flower==daffodils, and color==yellow.
    for i in houses:
        s.add( (edu[i] == 0) == (flower[i] == 0) )
        s.add( (flower[i] == 0) == (color[i] == 0) )
    # Thus any house with edu==0 will have flower==0 and color==0.
    
    # Clue (13): "Arnold is the person who loves yellow."
    # Name 0 corresponds to Arnold and color 0 corresponds to yellow.
    for i in houses:
        s.add(Implies(name[i] == 0, color[i] == 0))
    # (Since all attributes are distinct, the only house with yellow will be the one with Arnold.)

    # Clue (3): "The person with a master's degree is Alice."
    # Education 1 = master and Name 3 = Alice.
    for i in houses:
        s.add(Implies(edu[i] == 1, name[i] == 3))
        
    # Clue (4): "The person with a master's degree is directly left of the person who loves classical music."
    # For houses 0..2: if a house has master then the next house's music must be classical (music==3). 
    for i in range(3):
        s.add(Implies(edu[i] == 1, music[i+1] == 3))
    # Master's cannot be in the last house because there would be no neighbor.
    s.add(edu[3] != 1)

    # Clue (2): "The person who loves a carnations arrangement is not in the first house."
    # Flower 1 = carnations.
    s.add(flower[0] != 1)

    # Clue (5): "Eric is not in the second house." (Name 2 = Eric)
    s.add(name[1] != 2)

    # Clue (6): "Arnold is not in the third house." (Name 0 = Arnold)
    s.add(name[2] != 0)

    # Clue (7): "The person who loves yellow is directly left of the person who loves the rose bouquet."
    # If a house has yellow (color==0) then the next house must have roses (flower==2).
    for i in range(3):
        s.add(Implies(color[i] == 0, flower[i+1] == 2))
    
    # Clue (8): "The person who loves pop music is in the second house."
    # Music 2 = pop.
    s.add(music[1] == 2)

    # Clue (9): "The person with an associate's degree is not in the fourth house."
    # Education 3 = associate.
    s.add(edu[3] != 3)

    # Clue (10): "The person who loves a carnations arrangement is not in the fourth house."
    s.add(flower[3] != 1)

    # Clue (11): "The person whose favorite color is red is directly left of the person who loves white."
    # Color 2 = red, Color 3 = white.
    for i in range(3):
        s.add(Implies(color[i] == 2, color[i+1] == 3))
    # Also, red cannot be in the last house.
    s.add(color[3] != 2)

    # Clue (12): "The person whose favorite color is red is the person who loves rock music."
    # Music 1 = rock.
    for i in houses:
        s.add(Implies(color[i] == 2, music[i] == 1))
    
    # --- End of clues ---

    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        # Decoding dictionaries for the integer values.
        names_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice"}
        edu_map = {0: "bachelor", 1: "master", 2: "high school", 3: "associate"}
        music_map = {0: "jazz", 1: "rock", 2: "pop", 3: "classical"}
        color_map = {0: "yellow", 1: "green", 2: "red", 3: "white"}
        flower_map = {0: "daffodils", 1: "carnations", 2: "roses", 3: "lilies"}
        
        solution_rows = []
        for i in houses:
            row = [
                str(i+1),
                names_map[m.evaluate(name[i]).as_long()],
                edu_map[m.evaluate(edu[i]).as_long()],
                music_map[m.evaluate(music[i]).as_long()],
                color_map[m.evaluate(color[i]).as_long()],
                flower_map[m.evaluate(flower[i]).as_long()]
            ]
            solution_rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()