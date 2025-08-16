from z3 import *

def main():
    # Define enums for names, hair colors, and music genres
    NameSort, (Eric, Arnold, Peter, Alice) = EnumSort('Name', ['Eric', 'Arnold', 'Peter', 'Alice'])
    HairSort, (blonde, black, brown, red) = EnumSort('Hair', ['blonde', 'black', 'brown', 'red'])
    MusicSort, (pop, jazz, rock, classical) = EnumSort('Music', ['pop', 'jazz', 'rock', 'classical'])
    
    # Create dictionaries for converting enums to strings
    name_dict = { Eric: "Eric", Arnold: "Arnold", Peter: "Peter", Alice: "Alice" }
    hair_dict = { blonde: "blonde", black: "black", brown: "brown", red: "red" }
    music_dict = { pop: "pop", jazz: "jazz", rock: "rock", classical: "classical" }
    
    # Create lists to hold attributes for each house (index 0 = house1, 1 = house2, etc.)
    names = [Const(f'name_{i}', NameSort) for i in range(4)]
    hairs = [Const(f'hair_{i}', HairSort) for i in range(4)]
    musics = [Const(f'music_{i}', MusicSort) for i in range(4)]
    
    s = Solver()
    
    # All attributes must be distinct
    s.add(Distinct(names))
    s.add(Distinct(hairs))
    s.add(Distinct(musics))
    
    # Clue 1: Eric has red hair
    for i in range(4):
        s.add(Implies(names[i] == Eric, hairs[i] == red))
        s.add(Implies(hairs[i] == red, names[i] == Eric))
    
    # Clue 5: Classical music is in house 1
    s.add(musics[0] == classical)
    # Clue 2: Classical is directly left of blonde hair, so blonde hair in house 2
    s.add(hairs[1] == blonde)
    
    # Clue 3: Brown hair not in house 1
    s.add(hairs[0] != brown)
    
    # Clue 4: Pop music not in house 3
    s.add(musics[2] != pop)
    
    # Clue 6: Jazz music is the person with red hair
    for i in range(4):
        s.add(Implies(musics[i] == jazz, hairs[i] == red))
        s.add(Implies(hairs[i] == red, musics[i] == jazz))
    
    # Clue 7: Rock music is Arnold
    for i in range(4):
        s.add(Implies(musics[i] == rock, names[i] == Arnold))
        s.add(Implies(names[i] == Arnold, musics[i] == rock))
    
    # Clue 8: Peter is to the right of the rock lover (Arnold)
    # Arnold (rock) must be in a house with index less than Peter's house index
    s.add(Or(
        And(names[0] == Arnold, Or(names[1] == Peter, names[2] == Peter, names[3] == Peter)),
        And(names[1] == Arnold, Or(names[2] == Peter, names[3] == Peter)),
        And(names[2] == Arnold, names[3] == Peter)
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = m.eval(names[i])
            hair_val = m.eval(hairs[i])
            music_val = m.eval(musics[i])
            name_str = name_dict[name_val.as_long()]
            hair_str = hair_dict[hair_val.as_long()]
            music_str = music_dict[music_val.as_long()]
            rows.append([house_num, name_str, hair_str, music_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()