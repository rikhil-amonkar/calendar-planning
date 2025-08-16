from z3 import *
import json

def main():
    # Define the lists of names and music genres
    names_list = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    music_list = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
    
    # Create enum sorts
    Name, name_consts = EnumSort('Name', names_list)
    Music, music_consts = EnumSort('Music', music_list)
    
    # Unpack the constants for names
    Arnold, Eric, Peter, Alice, Carol, Bob = name_consts
    # Unpack the constants for music
    jazz, pop, classical, rock, hip_hop, country = music_consts
    
    # Create variables for each house: n0 to n5 for names, m0 to m5 for music
    n = [Const(f'n{i}', Name) for i in range(6)]
    m = [Const(f'm{i}', Music) for i in range(6)]
    
    s = Solver()
    
    # Each house has a different person and a different music genre
    s.add(Distinct(n))
    s.add(Distinct(m))
    
    # Clue 3: Carol is in the sixth house.
    s.add(n[5] == Carol)
    
    # Clue 5: The person who loves country music is Carol.
    s.add(m[5] == country)
    
    # Clue 9: The person who loves hip-hop music is in the third house.
    s.add(m[2] == hip_hop)
    
    # Clue 1: Bob is directly left of the person who loves jazz music.
    s.add(Or(
        And(n[0] == Bob, m[1] == jazz),
        And(n[1] == Bob, m[2] == jazz),
        And(n[2] == Bob, m[3] == jazz),
        And(n[3] == Bob, m[4] == jazz),
        And(n[4] == Bob, m[5] == jazz)
    ))
    
    # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music.
    # Clue 4: Eric and the person who loves hip-hop music are next to each other.
    # We define integer positions for Eric and hip-hop
    Eric_house = Int('Eric_house')
    s.add(Eric_house >= 1, Eric_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Eric, Eric_house == i+1, True))
    
    hip_hop_house = Int('hip_hop_house')
    s.add(hip_hop_house >= 1, hip_hop_house <= 6)
    for i in range(6):
        s.add(If(m[i] == hip_hop, hip_hop_house == i+1, True))
    
    s.add(Eric_house < hip_hop_house)  # Clue 2
    s.add(Or(Eric_house == hip_hop_house - 1, Eric_house == hip_hop_house + 1))  # Clue 4
    
    # Clue 6: Arnold is not in the fifth house.
    s.add(n[4] != Arnold)
    
    # Clue 7: Arnold is somewhere to the right of the person who loves pop music.
    # Clue 8: The person who loves pop music is Peter.
    pop_house = Int('pop_house')
    s.add(pop_house >= 1, pop_house <= 6)
    for i in range(6):
        s.add(If(m[i] == pop, pop_house == i+1, True))
    
    Arnold_house = Int('Arnold_house')
    s.add(Arnold_house >= 1, Arnold_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Arnold, Arnold_house == i+1, True))
    
    s.add(pop_house < Arnold_house)  # Clue 7
    
    # For Clue 8: also enforce that Peter has pop music
    for i in range(6):
        s.add(If(n[i] == Peter, m[i] == pop, True))
    
    # Clue 10: There is one house between Peter and Bob.
    Peter_house = Int('Peter_house')
    s.add(Peter_house >= 1, Peter_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Peter, Peter_house == i+1, True))
    
    Bob_house = Int('Bob_house')
    s.add(Bob_house >= 1, Bob_house <= 6)
    for i in range(6):
        s.add(If(n[i] == Bob, Bob_house == i+1, True))
    
    s.add(Or(Peter_house == Bob_house + 2, Peter_house == Bob_house - 2))
    
    # Clue 11: The person who loves rock music is not in the fifth house.
    s.add(m[4] != rock)
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(6):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            music_val = model.eval(m[i])
            name_str = name_val.decl().name()
            music_str = music_val.decl().name()
            rows.append([house_num, name_str, music_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()