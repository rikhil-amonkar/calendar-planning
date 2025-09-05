from z3 import *
import json

def main():
    # Define the categories and their options
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    
    # Create Z3 variables for the house of each attribute
    n_house = [Int('n_' + name) for name in names]
    f_house = [Int('f_' + flower) for flower in flowers]
    a_house = [Int('a_' + animal) for animal in animals]
    
    s = Solver()
    
    # All houses must be between 1 and 5
    for var in n_house + f_house + a_house:
        s.add(var >= 1, var <= 5)
    
    # Each set of attributes must have distinct houses
    s.add(Distinct(n_house))
    s.add(Distinct(f_house))
    s.add(Distinct(a_house))
    
    # Clue 1: Alice is in the second house.
    s.add(n_house[names.index('Alice')] == 2)
    
    # Clue 2: The person who loves the bouquet of lilies is the bird keeper.
    s.add(f_house[flowers.index('lilies')] == a_house[animals.index('bird')])
    
    # Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips.
    s.add(n_house[names.index('Peter')] > f_house[flowers.index('tulips')])
    
    # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils.
    s.add(a_house[animals.index('fish')] == f_house[flowers.index('daffodils')])
    
    # Clue 5: The person who keeps horses is Eric.
    s.add(a_house[animals.index('horse')] == n_house[names.index('Eric')])
    
    # Clue 6: There are two houses between the dog owner and Bob.
    dog_house = a_house[animals.index('dog')]
    bob_house = n_house[names.index('Bob')]
    s.add(Or(dog_house - bob_house == 3, bob_house - dog_house == 3))
    
    # Clue 7: The fish enthusiast is directly left of Bob.
    s.add(a_house[animals.index('fish')] + 1 == bob_house)
    
    # Clue 8: Alice is directly left of the person who keeps horses.
    s.add(n_house[names.index('Alice')] + 1 == a_house[animals.index('horse')])
    
    # Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
    s.add(f_house[flowers.index('carnations')] + 1 == f_house[flowers.index('tulips')])
    
    # Clue 10: The cat lover is not in the first house.
    s.add(a_house[animals.index('cat')] != 1)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        solution_rows = []
        for house_num in range(1, 6):
            # Find the name for this house
            name_val = next(name for idx, name in enumerate(names) if m.evaluate(n_house[idx]).as_long() == house_num)
            # Find the flower for this house
            flower_val = next(flower for idx, flower in enumerate(flowers) if m.evaluate(f_house[idx]).as_long() == house_num)
            # Find the animal for this house
            animal_val = next(animal for idx, animal in enumerate(animals) if m.evaluate(a_house[idx]).as_long() == house_num)
            solution_rows.append([str(house_num), name_val, flower_val, animal_val])
        
        # Format the solution as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()