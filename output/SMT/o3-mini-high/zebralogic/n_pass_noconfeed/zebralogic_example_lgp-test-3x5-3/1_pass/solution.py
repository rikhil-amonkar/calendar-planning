from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 3

    # Create variables for each category for each house (houses are indexed 0, 1, 2)
    names = [Int(f"name_{i}") for i in range(num_houses)]
    smoothies = [Int(f"smoothie_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]
    animals = [Int(f"animal_{i}") for i in range(num_houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(num_houses)]

    # Domain constraints: each variable must be in {1, 2, 3}
    for var in names + smoothies + flowers + animals + hobbies:
        solver.add(var >= 1, var <= 3)

    # All-different constraints for each category
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(flowers))
    solver.add(Distinct(animals))
    solver.add(Distinct(hobbies))
    
    # For each house, add the clues that relate to that house.
    for i in range(num_houses):
        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
        # Mapping: bird=3, cherry=1.
        solver.add(Implies(animals[i] == 3, smoothies[i] == 1))
        solver.add(Implies(smoothies[i] == 1, animals[i] == 3))
        
        # Clue 3: The person who loves cooking is the Desert smoothie lover.
        # Mapping: cooking=2, desert=3.
        solver.add(Implies(hobbies[i] == 2, smoothies[i] == 3))
        solver.add(Implies(smoothies[i] == 3, hobbies[i] == 2))
        
        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
        # Mapping: gardening=3, carnations=1.
        solver.add(Implies(hobbies[i] == 3, flowers[i] == 1))
        solver.add(Implies(flowers[i] == 1, hobbies[i] == 3))
        
        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
        # Mapping: daffodils=3, desert=3.
        solver.add(Implies(flowers[i] == 3, smoothies[i] == 3))
        solver.add(Implies(smoothies[i] == 3, flowers[i] == 3))
        
        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
        # Mapping: watermelon=2, horse=2.
        solver.add(Implies(smoothies[i] == 2, animals[i] == 2))
        solver.add(Implies(animals[i] == 2, smoothies[i] == 2))
        
        # Clue 8: The photography enthusiast is Eric.
        # Mapping: photography=1, Eric=1.
        solver.add(Implies(hobbies[i] == 1, names[i] == 1))
        solver.add(Implies(names[i] == 1, hobbies[i] == 1))
    
    # Clue 5: The person who loves cooking is directly left of Peter.
    # For house index 0: if cooking then house1 is Peter; for index 1: if cooking then house2 is Peter.
    solver.add(Implies(hobbies[0] == 2, names[1] == 2))
    solver.add(Implies(hobbies[1] == 2, names[2] == 2))
    # The cooking enthusiast cannot be in the rightmost house.
    solver.add(hobbies[2] != 2)
    
    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    # That is, the house with horse (animal == 2) must be adjacent to the house with photography (hobby == 1).
    solver.add(Or(
        And(animals[0] == 2, hobbies[1] == 1),
        And(animals[1] == 2, Or(hobbies[0] == 1, hobbies[2] == 1)),
        And(animals[2] == 2, hobbies[1] == 1)
    ))
    
    # Check if the puzzle is solvable
    if solver.check() == sat:
        m = solver.model()
        # Mappings for converting integer values back to their corresponding attributes.
        names_map = {1: "Eric", 2: "Peter", 3: "Arnold"}
        smoothies_map = {1: "cherry", 2: "watermelon", 3: "desert"}
        flowers_map = {1: "carnations", 2: "lilies", 3: "daffodils"}
        animals_map = {1: "cat", 2: "horse", 3: "bird"}
        hobbies_map = {1: "photography", 2: "cooking", 3: "gardening"}
        
        # Build the result rows: Maintain the order of houses (1, 2, 3)
        rows = []
        for i in range(num_houses):
            house_num = str(i + 1)
            name_val = names_map[m.evaluate(names[i]).as_long()]
            smoothie_val = smoothies_map[m.evaluate(smoothies[i]).as_long()]
            flower_val = flowers_map[m.evaluate(flowers[i]).as_long()]
            animal_val = animals_map[m.evaluate(animals[i]).as_long()]
            hobby_val = hobbies_map[m.evaluate(hobbies[i]).as_long()]
            rows.append([house_num, name_val, smoothie_val, flower_val, animal_val, hobby_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()