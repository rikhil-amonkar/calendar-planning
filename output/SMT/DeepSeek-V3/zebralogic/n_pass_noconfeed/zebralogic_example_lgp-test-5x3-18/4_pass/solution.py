import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    n_houses = 5
    houses = list(range(1, n_houses + 1))
    
    # Define attributes
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    flower_vars = [z3.Int(f'flower_{i}') for i in houses]
    animal_vars = [z3.Int(f'animal_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(flower_vars[i-1] >= 0, flower_vars[i-1] < len(flowers)))
        solver.add(z3.And(animal_vars[i-1] >= 0, animal_vars[i-1] < len(animals)))
    
    # All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(flower_vars))
    solver.add(z3.Distinct(animal_vars))
    
    # Clue 1: Alice is in the second house.
    alice_idx = names.index('Alice')
    solver.add(name_vars[1] == alice_idx)
    
    # Clue 2: The person who loves the bouquet of lilies is the bird keeper.
    lilies_idx = flowers.index('lilies')
    bird_idx = animals.index('bird')
    for i in houses:
        solver.add(z3.Implies(flower_vars[i-1] == lilies_idx, animal_vars[i-1] == bird_idx))
    
    # Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips.
    peter_idx = names.index('Peter')
    tulips_idx = flowers.index('tulips')
    
    # Create position variables
    tulips_house = z3.Int('tulips_house')
    peter_house = z3.Int('peter_house')
    solver.add(tulips_house >= 1, tulips_house <= 5)
    solver.add(peter_house >= 1, peter_house <= 5)
    
    # Link the variables to actual positions
    for i in houses:
        solver.add(z3.Implies(flower_vars[i-1] == tulips_idx, tulips_house == i))
        solver.add(z3.Implies(name_vars[i-1] == peter_idx, peter_house == i))
    
    solver.add(peter_house > tulips_house)
    
    # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils.
    fish_idx = animals.index('fish')
    daffodils_idx = flowers.index('daffodils')
    for i in houses:
        solver.add(z3.Implies(animal_vars[i-1] == fish_idx, flower_vars[i-1] == daffodils_idx))
        solver.add(z3.Implies(flower_vars[i-1] == daffodils_idx, animal_vars[i-1] == fish_idx))
    
    # Clue 5: The person who keeps horses is Eric.
    horse_idx = animals.index('horse')
    eric_idx = names.index('Eric')
    for i in houses:
        solver.add(z3.Implies(animal_vars[i-1] == horse_idx, name_vars[i-1] == eric_idx))
    
    # Clue 6: There are two houses between the dog owner and Bob.
    dog_idx = animals.index('dog')
    bob_idx = names.index('Bob')
    
    dog_house = z3.Int('dog_house')
    bob_house = z3.Int('bob_house')
    solver.add(dog_house >= 1, dog_house <= 5)
    solver.add(bob_house >= 1, bob_house <= 5)
    
    for i in houses:
        solver.add(z3.Implies(animal_vars[i-1] == dog_idx, dog_house == i))
        solver.add(z3.Implies(name_vars[i-1] == bob_idx, bob_house == i))
    
    # Two houses between means |dog_house - bob_house| = 3
    solver.add(z3.Or(dog_house == bob_house + 3, dog_house == bob_house - 3))
    
    # Clue 7: The fish enthusiast is directly left of Bob.
    # This means fish is in house i, Bob is in house i+1
    fish_house = z3.Int('fish_house')
    solver.add(fish_house >= 1, fish_house <= 5)
    for i in houses:
        solver.add(z3.Implies(animal_vars[i-1] == fish_idx, fish_house == i))
    
    # Bob is directly right of fish
    solver.add(bob_house == fish_house + 1)
    
    # Clue 8: Alice is directly left of the person who keeps horses.
    horse_house = z3.Int('horse_house')
    solver.add(horse_house >= 1, horse_house <= 5)
    for i in houses:
        solver.add(z3.Implies(animal_vars[i-1] == horse_idx, horse_house == i))
    
    # Alice is directly left of horse keeper
    solver.add(horse_house == 3)  # Alice is in house 2, so horse must be in house 3
    
    # Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
    carnations_idx = flowers.index('carnations')
    for i in range(1, n_houses):
        solver.add(z3.Implies(flower_vars[i-1] == carnations_idx, flower_vars[i] == tulips_idx))
    
    # Clue 10: The cat lover is not in the first house.
    cat_idx = animals.index('cat')
    solver.add(animal_vars[0] != cat_idx)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for i in range(n_houses):
            house_num = str(i + 1)
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            flower_val = flowers[model.evaluate(flower_vars[i]).as_long()]
            animal_val = animals[model.evaluate(animal_vars[i]).as_long()]
            solution.append([house_num, name_val, flower_val, animal_val])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()