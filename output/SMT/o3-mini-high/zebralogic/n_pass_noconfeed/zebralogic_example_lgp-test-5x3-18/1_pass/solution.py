from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 5

    # Create integer variables for each house's attributes.
    # Each variable is in the range 0..4.
    names = [Int(f"name_{i}") for i in range(num_houses)]
    flowers = [Int(f"flower_{i}") for i in range(num_houses)]
    animals = [Int(f"animal_{i}") for i in range(num_houses)]
    
    # Domain constraints for each variable.
    for i in range(num_houses):
        solver.add(And(names[i] >= 0, names[i] < num_houses))
        solver.add(And(flowers[i] >= 0, flowers[i] < num_houses))
        solver.add(And(animals[i] >= 0, animals[i] < num_houses))
    
    # All-different constraints.
    solver.add(Distinct(names))
    solver.add(Distinct(flowers))
    solver.add(Distinct(animals))
    
    # Mappings (our internal representation):
    # Names: 0:Alice, 1:Eric, 2:Arnold, 3:Bob, 4:Peter
    # Flowers: 0:tulips, 1:roses, 2:lilies, 3:daffodils, 4:carnations
    # Animals: 0:dog, 1:horse, 2:cat, 3:bird, 4:fish

    # Clue 1: Alice is in the second house.
    solver.add(names[1] == 0)
    
    # Clue 2: The person who loves the bouquet of lilies is the bird keeper.
    for i in range(num_houses):
        solver.add((flowers[i] == 2) == (animals[i] == 3))
    
    # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils.
    for i in range(num_houses):
        solver.add((flowers[i] == 3) == (animals[i] == 4))
    
    # Clue 5: The person who keeps horses is Eric.
    for i in range(num_houses):
        solver.add((names[i] == 1) == (animals[i] == 1))
    
    # Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips.
    # For every house with tulips (flower 0) and every house with Peter (name 4),
    # the house index of Peter must be greater.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(flowers[i] == 0, names[j] == 4), j > i))
    
    # Clue 6: There are two houses between the dog owner and Bob.
    # Dog is animal 0, Bob is name 3.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(animals[i] == 0, names[j] == 3), Abs(i - j) == 3))
    
    # Clue 7: The fish enthusiast is directly left of Bob.
    # That means if a house has Bob (name 3), the house immediately to its left 
    # must have fish (animal 4).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 3, And(i > 0, animals[i - 1] == 4)))
    
    # Clue 8: Alice is directly left of the person who keeps horses.
    # If a house has Alice (name 0), then the immediate right house must have horse (animal 1).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 0, And(i < num_houses - 1, animals[i + 1] == 1)))
    
    # Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
    # Carnations is flower 4 and tulips is flower 0.
    for i in range(num_houses):
        solver.add(Implies(flowers[i] == 4, And(i < num_houses - 1, flowers[i + 1] == 0)))
    
    # Clue 10: The cat lover is not in the first house.
    # Cat is animal 2.
    solver.add(animals[0] != 2)
    
    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        # Mapping back to the original attribute names.
        names_list = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
        flowers_list = ["tulips", "roses", "lilies", "daffodils", "carnations"]
        animals_list = ["dog", "horse", "cat", "bird", "fish"]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": []
            }
        }
        
        # Houses are numbered 1 to 5 (left to right).
        for i in range(num_houses):
            house_num = str(i + 1)
            name_val = model.evaluate(names[i]).as_long()
            flower_val = model.evaluate(flowers[i]).as_long()
            animal_val = model.evaluate(animals[i]).as_long()
            solution["solution"]["rows"].append([
                house_num,
                names_list[name_val],
                flowers_list[flower_val],
                animals_list[animal_val]
            ])
        
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))
        
if __name__ == "__main__":
    main()