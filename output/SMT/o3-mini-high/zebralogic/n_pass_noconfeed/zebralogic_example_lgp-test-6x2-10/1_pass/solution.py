from z3 import *
import json

def main():
    solver = Solver()
    
    # Define integer codes for Names
    NAME_AR = 0  # Arnold
    NAME_ER = 1  # Eric
    NAME_PE = 2  # Peter
    NAME_AL = 3  # Alice
    NAME_CA = 4  # Carol
    NAME_BO = 5  # Bob

    # Define integer codes for Music Genres
    MUSIC_JAZZ      = 0
    MUSIC_POP       = 1
    MUSIC_CLASSICAL = 2
    MUSIC_ROCK      = 3
    MUSIC_HIP_HOP   = 4
    MUSIC_COUNTRY   = 5

    houses = 6
    # Create arrays of Z3 Int variables for names and music (0-indexed: house 1 is index 0, house 6 is index 5)
    name_vars = [Int(f"name_{i}") for i in range(houses)]
    music_vars = [Int(f"music_{i}") for i in range(houses)]

    # Domain constraints: each variable must be between 0 and 5
    for i in range(houses):
        solver.add(name_vars[i] >= 0, name_vars[i] < 6)
        solver.add(music_vars[i] >= 0, music_vars[i] < 6)
        
    # All names and music assignments must be distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(music_vars))

    # Clue 1: Bob is directly left of the person who loves jazz music.
    for i in range(houses - 1):
        solver.add(Implies(name_vars[i] == NAME_BO, music_vars[i+1] == MUSIC_JAZZ))
    solver.add(name_vars[houses - 1] != NAME_BO)  # Bob cannot be in the last house

    # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music.
    # (Since hip-hop is fixed to the third house in Clue 9, Eric must be in a house with index < 2.)
    for i in range(houses):
        solver.add(Implies(name_vars[i] == NAME_ER, i < 2))
    
    # Clue 3: Carol is in the sixth house.
    solver.add(name_vars[5] == NAME_CA)

    # Clue 4: Eric and the person who loves hip-hop music are next to each other.
    for i in range(houses):
        neighbors = []
        if i > 0:
            neighbors.append(music_vars[i-1] == MUSIC_HIP_HOP)
        if i < houses - 1:
            neighbors.append(music_vars[i+1] == MUSIC_HIP_HOP)
        if neighbors:
            solver.add(Implies(name_vars[i] == NAME_ER, Or(*neighbors)))
    
    # Clue 5: The person who loves country music is Carol.
    solver.add(music_vars[5] == MUSIC_COUNTRY)
    
    # Clue 6: Arnold is not in the fifth house.
    solver.add(name_vars[4] != NAME_AR)
    
    # Clue 7 and Clue 8:
    # - Clue 8: The person who loves pop music is Peter.
    # - Clue 7: Arnold is somewhere to the right of the person who loves pop music.
    # Enforce a bi-conditional: if a house's music is pop then its occupant is Peter and vice versa.
    for i in range(houses):
        solver.add(Implies(music_vars[i] == MUSIC_POP, name_vars[i] == NAME_PE))
        solver.add(Implies(name_vars[i] == NAME_PE, music_vars[i] == MUSIC_POP))
    
    # Introduce positional variables to compare locations for Peter, Arnold, and Bob.
    posPeter = Int("posPeter")
    posArnold = Int("posArnold")
    posBob    = Int("posBob")
    
    solver.add(And(posPeter >= 0, posPeter < houses))
    solver.add(And(posArnold >= 0, posArnold < houses))
    solver.add(And(posBob >= 0, posBob < houses))
    
    for i in range(houses):
        solver.add(Implies(name_vars[i] == NAME_PE, posPeter == i))
        solver.add(Implies(name_vars[i] == NAME_AR, posArnold == i))
        solver.add(Implies(name_vars[i] == NAME_BO, posBob == i))
    
    # Arnold (whose position is posArnold) must be to the right of the pop lover (Peter, posPeter).
    solver.add(posPeter < posArnold)
    
    # Clue 9: The person who loves hip-hop music is in the third house.
    solver.add(music_vars[2] == MUSIC_HIP_HOP)
    
    # Clue 10: There is one house between Peter and Bob.
    solver.add(Abs(posPeter - posBob) == 2)
    
    # Clue 11: The person who loves rock music is not in the fifth house.
    solver.add(music_vars[4] != MUSIC_ROCK)
    
    # Additional constraint: From Clues 2 and 4, Eric must be in a house with index < 2.
    # We fix Eric to the second house (index 1) to satisfy the "next to" requirement with the third house.
    solver.add(name_vars[1] == NAME_ER)
    
    if solver.check() == sat:
        model = solver.model()
        # Mapping integer codes back to actual names and music genres.
        names_map = {
            NAME_AR: "Arnold",
            NAME_ER: "Eric",
            NAME_PE: "Peter",
            NAME_AL: "Alice",
            NAME_CA: "Carol",
            NAME_BO: "Bob"
        }
        music_map = {
            MUSIC_JAZZ: "jazz",
            MUSIC_POP: "pop",
            MUSIC_CLASSICAL: "classical",
            MUSIC_ROCK: "rock",
            MUSIC_HIP_HOP: "hip hop",
            MUSIC_COUNTRY: "country"
        }
        
        rows = []
        # Houses are numbered 1 to 6 in order.
        for i in range(houses):
            house_num = str(i + 1)
            name_val = model.evaluate(name_vars[i]).as_long()
            music_val = model.evaluate(music_vars[i]).as_long()
            rows.append([house_num, names_map[name_val], music_map[music_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()