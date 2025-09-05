from z3 import *
import json

def main():
    # There are 2 houses indexed 0 (House "1") and 1 (House "2")
    num_houses = 2

    # Mapping indices: for Name: 0 = Eric, 1 = Arnold
    # BookGenre: 0 = science fiction, 1 = mystery
    # Birthday: 0 = april, 1 = sept
    # Animal: 0 = horse, 1 = cat

    # Create SMT variables for each house attribute
    Name = [Int(f"Name_{i}") for i in range(num_houses)]
    Genre = [Int(f"Genre_{i}") for i in range(num_houses)]
    Birthday = [Int(f"Birthday_{i}") for i in range(num_houses)]
    Animal = [Int(f"Animal_{i}") for i in range(num_houses)]
    
    solver = Solver()
    
    # Each attribute variable for each house must be 0 or 1
    for i in range(num_houses):
        solver.add(And(Name[i] >= 0, Name[i] < 2))
        solver.add(And(Genre[i] >= 0, Genre[i] < 2))
        solver.add(And(Birthday[i] >= 0, Birthday[i] < 2))
        solver.add(And(Animal[i] >= 0, Animal[i] < 2))
    
    # Ensure all attributes are unique across houses
    solver.add(Distinct(Name))
    solver.add(Distinct(Genre))
    solver.add(Distinct(Birthday))
    solver.add(Distinct(Animal))
    
    # Clue 1: Eric is in the first house (House 1 -> index 0)
    # Name: 0 represents Eric.
    solver.add(Name[0] == 0)
    
    # Clue 2: Eric is the person whose birthday is in September.
    # Birthday: 1 represents sept.
    for i in range(num_houses):
        solver.add(Implies(Name[i] == 0, Birthday[i] == 1))
    
    # Clue 3: The person who loves science fiction books is in the second house.
    # Genre: 0 represents science fiction.
    solver.add(Genre[1] == 0)
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September.
    # Animal: 0 represents horse.
    for i in range(num_houses):
        solver.add(Implies(Birthday[i] == 1, Animal[i] == 0))
        solver.add(Implies(Animal[i] == 0, Birthday[i] == 1))
    
    # Check the constraints and build the solution.
    if solver.check() == sat:
        model = solver.model()
        
        # Mapping arrays to print names, genres, birthdays, and animals.
        nameMapping = ["Eric", "Arnold"]
        genreMapping = ["science fiction", "mystery"]
        birthdayMapping = ["april", "sept"]
        animalMapping = ["horse", "cat"]
        
        rows = []
        # House order: 1 then 2.
        for i in range(num_houses):
            house_num = str(i + 1)
            house_name = nameMapping[model[Name[i]].as_long()]
            house_genre = genreMapping[model[Genre[i]].as_long()]
            house_birthday = birthdayMapping[model[Birthday[i]].as_long()]
            house_animal = animalMapping[model[Animal[i]].as_long()]
            rows.append([house_num, house_name, house_genre, house_birthday, house_animal])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "no solution found"}))

if __name__ == "__main__":
    main()