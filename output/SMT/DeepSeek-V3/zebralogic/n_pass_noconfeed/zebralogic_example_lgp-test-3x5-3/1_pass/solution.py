import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{h}') for h in houses]
    smoothie_vars = [Int(f'smoothie_{h}') for h in houses]
    flower_vars = [Int(f'flower_{h}') for h in houses]
    animal_vars = [Int(f'animal_{h}') for h in houses]
    hobby_vars = [Int(f'hobby_{h}') for h in houses]
    
    # Domain constraints - each attribute variable must be 0, 1, or 2
    for var in name_vars + smoothie_vars + flower_vars + animal_vars + hobby_vars:
        solver.add(var >= 0, var <= 2)
    
    # All attributes must be unique within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(flower_vars))
    solver.add(Distinct(animal_vars))
    solver.add(Distinct(hobby_vars))
    
    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    horse_house = Int('horse_house')
    photo_house = Int('photo_house')
    solver.add(horse_house >= 1, horse_house <= 3)
    solver.add(photo_house >= 1, photo_house <= 3)
    
    # Find which house has horse and which has photography
    for h in houses:
        solver.add(Implies(animal_vars[h-1] == animals.index('horse'), horse_house == h))
        solver.add(Implies(hobby_vars[h-1] == hobbies.index('photography'), photo_house == h))
    
    solver.add(Or(Abs(horse_house - photo_house) == 1))
    
    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for h in houses:
        bird_condition = (animal_vars[h-1] == animals.index('bird'))
        cherry_condition = (smoothie_vars[h-1] == smoothies.index('cherry'))
        solver.add(bird_condition == cherry_condition)
    
    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for h in houses:
        cooking_condition = (hobby_vars[h-1] == hobbies.index('cooking'))
        desert_condition = (smoothie_vars[h-1] == smoothies.index('desert'))
        solver.add(cooking_condition == desert_condition)
    
    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    for h in houses:
        gardening_condition = (hobby_vars[h-1] == hobbies.index('gardening'))
        carnations_condition = (flower_vars[h-1] == flowers.index('carnations'))
        solver.add(gardening_condition == carnations_condition)
    
    # Clue 5: The person who loves cooking is directly left of Peter.
    cooking_house = Int('cooking_house')
    peter_house = Int('peter_house')
    solver.add(cooking_house >= 1, cooking_house <= 3)
    solver.add(peter_house >= 1, peter_house <= 3)
    
    for h in houses:
        solver.add(Implies(hobby_vars[h-1] == hobbies.index('cooking'), cooking_house == h))
        solver.add(Implies(name_vars[h-1] == names.index('Peter'), peter_house == h))
    
    solver.add(peter_house == cooking_house + 1)
    
    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for h in houses:
        daffodils_condition = (flower_vars[h-1] == flowers.index('daffodils'))
        desert_condition = (smoothie_vars[h-1] == smoothies.index('desert'))
        solver.add(daffodils_condition == desert_condition)
    
    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for h in houses:
        watermelon_condition = (smoothie_vars[h-1] == smoothies.index('watermelon'))
        horse_condition = (animal_vars[h-1] == animals.index('horse'))
        solver.add(watermelon_condition == horse_condition)
    
    # Clue 8: The photography enthusiast is Eric.
    for h in houses:
        photo_condition = (hobby_vars[h-1] == hobbies.index('photography'))
        eric_condition = (name_vars[h-1] == names.index('Eric'))
        solver.add(photo_condition == eric_condition)
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare result
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }
        
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[h-1]).as_long()
            flower_idx = model.evaluate(flower_vars[h-1]).as_long()
            animal_idx = model.evaluate(animal_vars[h-1]).as_long()
            hobby_idx = model.evaluate(hobby_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                smoothies[smoothie_idx],
                flowers[flower_idx],
                animals[animal_idx],
                hobbies[hobby_idx]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()