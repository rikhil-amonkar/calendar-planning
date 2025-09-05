from z3 import *
import json

def main():
    solver = Solver()
    houses = 6

    # Create Z3 integer variables for each house's attributes.
    names = [Int(f"name_{i}") for i in range(houses)]
    styles = [Int(f"style_{i}") for i in range(houses)]
    music = [Int(f"music_{i}") for i in range(houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(houses)]
    
    # Each variable must be between 0 and 5 (inclusive lower bound, exclusive upper bound).
    for i in range(houses):
        solver.add(names[i] >= 0, names[i] < houses)
        solver.add(styles[i] >= 0, styles[i] < houses)
        solver.add(music[i] >= 0, music[i] < houses)
        solver.add(hobbies[i] >= 0, hobbies[i] < houses)
    
    # All attributes must be unique across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(styles))
    solver.add(Distinct(music))
    solver.add(Distinct(hobbies))
    
    # Mapping of indices to actual names/attributes.
    # Names: 0: Eric, 1: Alice, 2: Arnold, 3: Carol, 4: Peter, 5: Bob
    # HouseStyle: 0: mediterranean, 1: modern, 2: craftsman, 3: ranch, 4: colonial, 5: victorian
    # MusicGenre: 0: country, 1: hip hop, 2: pop, 3: jazz, 4: classical, 5: rock
    # Hobby: 0: cooking, 1: painting, 2: photography, 3: woodworking, 4: gardening, 5: knitting

    # Clue 1: The person who loves rock music is in the fifth house.
    # House numbering: index 4 corresponds to the 5th house.
    solver.add(music[4] == 5)
    
    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    # Classical music has index 4 and woodworking hobby has index 3.
    for i in range(houses):
        if i == 0:
            solver.add(Implies(music[i] == 4, hobbies[i+1] == 3))
        elif i == houses - 1:
            solver.add(Implies(music[i] == 4, hobbies[i-1] == 3))
        else:
            solver.add(Implies(music[i] == 4, Or(hobbies[i-1] == 3, hobbies[i+1] == 3)))
    for i in range(houses):
        if i == 0:
            solver.add(Implies(hobbies[i] == 3, music[i+1] == 4))
        elif i == houses - 1:
            solver.add(Implies(hobbies[i] == 3, music[i-1] == 4))
        else:
            solver.add(Implies(hobbies[i] == 3, Or(music[i-1] == 4, music[i+1] == 4)))
    
    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
    # Mediterranean style has index 0 and hip hop has index 1.
    for i in range(houses):
        solver.add(Implies(styles[i] == 0, music[i] == 1))
        solver.add(Implies(music[i] == 1, styles[i] == 0))
    
    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
    # Arnold has index 2 and victorian style has index 5.
    for i in range(houses):
        for j in range(houses):
            if abs(i - j) != 3:
                solver.add(Not(And(names[i] == 2, styles[j] == 5)))
    
    # Clue 5: The person who loves jazz music is directly left of Eric.
    # Jazz has index 3 and Eric has index 0.
    for i in range(1, houses):
        solver.add(Implies(names[i] == 0, music[i-1] == 3))
    for i in range(houses - 1):
        solver.add(Implies(music[i] == 3, names[i+1] == 0))
    
    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    # Hip hop has index 1, and knitting has index 5.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(music[i] == 1, hobbies[j] == 5), i < j))
    
    # Clue 7: Carol is the person who loves hip-hop music.
    # Carol has index 3.
    for i in range(houses):
        solver.add(Implies(names[i] == 3, music[i] == 1))
    
    # Clue 8: The person in a Craftsman-style house is Arnold.
    # Craftsman style has index 2.
    for i in range(houses):
        solver.add(Implies(styles[i] == 2, names[i] == 2))
    
    # Clue 9: The person in a ranch-style home is Eric.
    # Ranch style has index 3.
    for i in range(houses):
        solver.add(Implies(styles[i] == 3, names[i] == 0))
    
    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
    # Woodworking hobby has index 3 and victorian style has index 5.
    for i in range(houses):
        solver.add(Implies(hobbies[i] == 3, styles[i] == 5))
        solver.add(Implies(styles[i] == 5, hobbies[i] == 3))
    
    # Clue 11: The person who loves country music is in the first house.
    # Country music has index 0 and the first house is index 0.
    solver.add(music[0] == 0)
    
    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    # Painting has index 1 and colonial style has index 4.
    for i in range(houses):
        for j in range(houses):
            if abs(i - j) != 2:
                solver.add(Not(And(hobbies[i] == 1, styles[j] == 4)))
    
    # Clue 13: Alice is the photography enthusiast.
    # Alice has index 1 and photography has index 2.
    for i in range(houses):
        solver.add(Implies(names[i] == 1, hobbies[i] == 2))
    
    # Clue 14: The person who enjoys gardening is Eric.
    # Gardening has index 4.
    for i in range(houses):
        solver.add(Implies(names[i] == 0, hobbies[i] == 4))
    
    # Clue 15: Bob is in the third house.
    # Bob has index 5 and the third house is index 2.
    solver.add(names[2] == 5)
    
    # Attempt to solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        possible_names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
        possible_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
        possible_music = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
        possible_hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]
        
        rows = []
        for i in range(houses):
            house_number = str(i+1)
            name_val = possible_names[model.evaluate(names[i]).as_long()]
            style_val = possible_styles[model.evaluate(styles[i]).as_long()]
            music_val = possible_music[model.evaluate(music[i]).as_long()]
            hobby_val = possible_hobbies[model.evaluate(hobbies[i]).as_long()]
            rows.append([house_number, name_val, style_val, music_val, hobby_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()