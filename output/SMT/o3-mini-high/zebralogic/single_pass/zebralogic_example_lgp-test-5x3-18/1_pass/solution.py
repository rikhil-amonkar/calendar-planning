from z3 import *
import json

def main():
    houses = 5
    # For names, we use:
    # 0: Alice, 1: Eric, 2: Arnold, 3: Bob, 4: Peter
    #
    # For flowers, we use:
    # 0: tulips, 1: roses, 2: lilies, 3: daffodils, 4: carnations
    #
    # For animals, we use:
    # 0: dog, 1: horse, 2: cat, 3: bird, 4: fish
    
    # Create Z3 int arrays for each attribute, one per house (houses are indexed 0..4 corresponding to House 1..5)
    names = [Int(f"name_{i}") for i in range(houses)]
    flowers = [Int(f"flower_{i}") for i in range(houses)]
    animals = [Int(f"animal_{i}") for i in range(houses)]
    
    s = Solver()
    
    # Domain constraints: each variable must be in the range 0..4
    for i in range(houses):
        s.add(And(names[i] >= 0, names[i] <= 4))
        s.add(And(flowers[i] >= 0, flowers[i] <= 4))
        s.add(And(animals[i] >= 0, animals[i] <= 4))
    
    # All houses have distinct names, flowers, and animals.
    s.add(Distinct(names))
    s.add(Distinct(flowers))
    s.add(Distinct(animals))
    
    # Clue 1: Alice is in the second house.
    # Alice is 0 and second house is index 1.
    s.add(names[1] == 0)
    
    # Clue 2: The person who loves the bouquet of lilies (flower 2) is the bird keeper (animal 3).
    for i in range(houses):
        s.add(Implies(flowers[i] == 2, animals[i] == 3))
        s.add(Implies(animals[i] == 3, flowers[i] == 2))
        
    # Clue 3: Peter (name 4) is somewhere to the right of the person who loves the vase of tulips (flower 0).
    # For any house i with Peter and any house j with tulips, we require i > j.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(names[i] == 4, flowers[j] == 0), i > j))
    
    # Clue 4: The fish enthusiast (animal 4) is the person who loves a bouquet of daffodils (flower 3).
    for i in range(houses):
        s.add(Implies(animals[i] == 4, flowers[i] == 3))
        s.add(Implies(flowers[i] == 3, animals[i] == 4))
    
    # Clue 5: The person who keeps horses (animal 1) is Eric (name 1).
    for i in range(houses):
        s.add(Implies(animals[i] == 1, names[i] == 1))
        s.add(Implies(names[i] == 1, animals[i] == 1))
    
    # Clue 6: There are two houses between the dog owner (animal 0) and Bob (name 3).
    # That means the difference in their house indices is exactly 3.
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(names[i] == 3, animals[j] == 0), Abs(i - j) == 3))
    
    # Clue 7: The fish enthusiast (animal 4) is directly left of Bob (name 3).
    # So if a house i has fish then the very next house (i+1) must have Bob.
    for i in range(houses - 1):
        s.add(Implies(animals[i] == 4, names[i+1] == 3))
    
    # Clue 8: Alice (name 0) is directly left of the person who keeps horses (animal 1).
    for i in range(houses - 1):
        s.add(Implies(names[i] == 0, animals[i+1] == 1))
    
    # Clue 9: The person who loves a carnations arrangement (flower 4) is directly left of the person who loves the vase of tulips (flower 0).
    for i in range(houses - 1):
        s.add(Implies(flowers[i] == 4, flowers[i+1] == 0))
    
    # Clue 10: The cat lover (animal 2) is not in the first house.
    s.add(animals[0] != 2)
    
    if s.check() == sat:
        m = s.model()
        # Prepare mapping lists for pretty-printing the solution.
        nameList = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
        flowerList = ["tulips", "roses", "lilies", "daffodils", "carnations"]
        animalList = ["dog", "horse", "cat", "bird", "fish"]
        
        # Build the solution rows in house order (House 1 to House 5)
        rows = []
        for i in range(houses):
            house_num = str(i + 1)
            # m[names[i]] is an IntNumRef, convert to int using as_long()
            house_name = nameList[m[names[i]].as_long()]
            house_flower = flowerList[m[flowers[i]].as_long()]
            house_animal = animalList[m[animals[i]].as_long()]
            rows.append([house_num, house_name, house_flower, house_animal])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": rows
            }
        }
        # Print the final JSON solution.
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()