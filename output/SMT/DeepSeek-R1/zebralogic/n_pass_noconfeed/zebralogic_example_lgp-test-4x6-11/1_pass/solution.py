import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Houses
    houses = [1, 2, 3, 4]
    
    # Attributes with integer mappings
    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    book_genres = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    music_genres = ["pop", "rock", "classical", "jazz"]
    
    # Create integer variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    hobby_vars = [Int(f"hobby_{i}") for i in houses]
    animal_vars = [Int(f"animal_{i}") for i in houses]
    book_vars = [Int(f"book_{i}") for i in houses]
    birthday_vars = [Int(f"birthday_{i}") for i in houses]
    music_vars = [Int(f"music_{i}") for i in houses]
    
    # All variables must be between 1 and 4
    for var in name_vars + hobby_vars + animal_vars + book_vars + birthday_vars + music_vars:
        s.add(var >= 1, var <= 4)
    
    # Each attribute must have distinct values across houses
    s.add(Distinct(name_vars))
    s.add(Distinct(hobby_vars))
    s.add(Distinct(animal_vars))
    s.add(Distinct(book_vars))
    s.add(Distinct(birthday_vars))
    s.add(Distinct(music_vars))
    
    # Clue 1: Cooking hobby same as romance books
    for i in houses:
        s.add((hobby_vars[i-1] == 1) == (book_vars[i-1] == 3))
    
    # Clue 2: February birthday same as pop music
    for i in houses:
        s.add((birthday_vars[i-1] == 4) == (music_vars[i-1] == 1))
    
    # Clue 3: Eric not in second house
    s.add(name_vars[1] != 3)
    
    # Clue 4: Romance books not in fourth house
    s.add(book_vars[3] != 3)
    
    # Clue 5: February birthday same as fish animal
    for i in houses:
        s.add((birthday_vars[i-1] == 4) == (animal_vars[i-1] == 2))
    
    # Clue 6: Alice right of fantasy books
    alice_house = Int("alice_house")
    fantasy_house = Int("fantasy_house")
    s.add(alice_house >= 1, alice_house <= 4)
    s.add(fantasy_house >= 1, fantasy_house <= 4)
    for i in houses:
        s.add(If(name_vars[i-1] == 2, alice_house == i, True))
        s.add(If(book_vars[i-1] == 1, fantasy_house == i, True))
    s.add(alice_house > fantasy_house)
    
    # Clue 7: Horse animal same as rock music
    for i in houses:
        s.add((animal_vars[i-1] == 1) == (music_vars[i-1] == 2))
    
    # Clue 8: Gardening hobby same as April birthday
    for i in houses:
        s.add((hobby_vars[i-1] == 3) == (birthday_vars[i-1] == 1))
    
    # Clue 9: Jazz music same as cooking hobby
    for i in houses:
        s.add((music_vars[i-1] == 4) == (hobby_vars[i-1] == 1))
    
    # Clue 10: Rock music same as mystery books
    for i in houses:
        s.add((music_vars[i-1] == 2) == (book_vars[i-1] == 2))
    
    # Clue 11: Painting hobby directly left of romance books
    painting_house = Int("painting_house")
    romance_house = Int("romance_house")
    s.add(painting_house >= 1, painting_house <= 3)
    s.add(romance_house >= 2, romance_house <= 4)
    for i in houses:
        s.add(If(hobby_vars[i-1] == 2, painting_house == i, True))
        s.add(If(book_vars[i-1] == 3, romance_house == i, True))
    s.add(romance_house == painting_house + 1)
    
    # Clue 12: Peter same as pop music
    for i in houses:
        s.add((name_vars[i-1] == 1) == (music_vars[i-1] == 1))
    
    # Clue 13: Gardening hobby is Arnold
    for i in houses:
        s.add((hobby_vars[i-1] == 3) == (name_vars[i-1] == 4))
    
    # Clue 14: Rock music directly left of January birthday
    rock_house = Int("rock_house")
    jan_house = Int("jan_house")
    s.add(rock_house >= 1, rock_house <= 3)
    s.add(jan_house >= 2, jan_house <= 4)
    for i in houses:
        s.add(If(music_vars[i-1] == 2, rock_house == i, True))
        s.add(If(birthday_vars[i-1] == 2, jan_house == i, True))
    s.add(jan_house == rock_house + 1)
    
    # Clue 15: Cooking hobby not in third house
    s.add(hobby_vars[2] != 1)
    
    # Clue 16: Cat animal right of horse animal
    cat_house = Int("cat_house")
    horse_house = Int("horse_house")
    s.add(cat_house >= 1, cat_house <= 4)
    s.add(horse_house >= 1, horse_house <= 4)
    for i in houses:
        s.add(If(animal_vars[i-1] == 3, cat_house == i, True))
        s.add(If(animal_vars[i-1] == 1, horse_house == i, True))
    s.add(cat_house > horse_house)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Map house indices to attribute values
        solution = []
        for i in houses:
            house_sol = [str(i)]
            # Name
            name_val = m.evaluate(name_vars[i-1]).as_long()
            house_sol.append(names[name_val-1])
            # Hobby
            hobby_val = m.evaluate(hobby_vars[i-1]).as_long()
            house_sol.append(hobbies[hobby_val-1])
            # Animal
            animal_val = m.evaluate(animal_vars[i-1]).as_long()
            house_sol.append(animals[animal_val-1])
            # Book genre
            book_val = m.evaluate(book_vars[i-1]).as_long()
            house_sol.append(book_genres[book_val-1])
            # Birthday
            birthday_val = m.evaluate(birthday_vars[i-1]).as_long()
            house_sol.append(birthdays[birthday_val-1])
            # Music genre
            music_val = m.evaluate(music_vars[i-1]).as_long()
            house_sol.append(music_genres[music_val-1])
            solution.append(house_sol)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()