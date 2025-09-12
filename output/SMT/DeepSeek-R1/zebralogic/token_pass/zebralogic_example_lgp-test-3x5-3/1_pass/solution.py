import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes with EnumSort
    Name, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    Smoothie, (cherry, watermelon, desert) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert'])
    Flower, (carnations, lilies, daffodils) = EnumSort('Flower', ['carnations', 'lilies', 'daffodils'])
    Animal, (cat, horse, bird) = EnumSort('Animal', ['cat', 'horse', 'bird'])
    Hobby, (photography, cooking, gardening) = EnumSort('Hobby', ['photography', 'cooking', 'gardening'])
    
    # Create variables for each house's attributes
    names = [Const(f'name_{i}', Name) for i in range(1,4)]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in range(1,4)]
    flowers = [Const(f'flower_{i}', Flower) for i in range(1,4)]
    animals = [Const(f'animal_{i}', Animal) for i in range(1,4)]
    hobbies = [Const(f'hobby_{i}', Hobby) for i in range(1,4)]
    
    # Add constraints: all attributes are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(flowers))
    solver.add(Distinct(animals))
    solver.add(Distinct(hobbies))
    
    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    for i in range(3):
        if i == 0:
            solver.add(Or(animals[i] == horse, animals[i+1] == horse))
        elif i == 2:
            solver.add(Or(animals[i] == horse, animals[i-1] == horse))
        else:
            solver.add(Or(And(animals[i] == horse, hobbies[i-1] == photography), 
                         And(animals[i] == horse, hobbies[i+1] == photography),
                         And(hobbies[i] == photography, animals[i-1] == horse),
                         And(hobbies[i] == photography, animals[i+1] == horse)))
    
    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for i in range(3):
        solver.add(If(animals[i] == bird, smoothies[i] == cherry, True))
        solver.add(If(smoothies[i] == cherry, animals[i] == bird, True))
    
    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for i in range(3):
        solver.add(If(hobbies[i] == cooking, smoothies[i] == desert, True))
        solver.add(If(smoothies[i] == desert, hobbies[i] == cooking, True))
    
    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    for i in range(3):
        solver.add(If(hobbies[i] == gardening, flowers[i] == carnations, True))
        solver.add(If(flowers[i] == carnations, hobbies[i] == gardening, True))
    
    # Clue 5: The person who loves cooking is directly left of Peter.
    for i in range(2):
        solver.add(If(hobbies[i] == cooking, names[i+1] == Peter, True))
    solver.add(Not(hobbies[2] == cooking))  # Cooking cannot be in last house
    
    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for i in range(3):
        solver.add(If(flowers[i] == daffodils, smoothies[i] == desert, True))
        solver.add(If(smoothies[i] == desert, flowers[i] == daffodils, True))
    
    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for i in range(3):
        solver.add(If(smoothies[i] == watermelon, animals[i] == horse, True))
        solver.add(If(animals[i] == horse, smoothies[i] == watermelon, True))
    
    # Clue 8: The photography enthusiast is Eric.
    for i in range(3):
        solver.add(If(hobbies[i] == photography, names[i] == Eric, True))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }
        
        # Map house numbers to their attribute values
        for i in range(3):
            name_val = model.eval(names[i])
            smoothie_val = model.eval(smoothies[i])
            flower_val = model.eval(flowers[i])
            animal_val = model.eval(animals[i])
            hobby_val = model.eval(hobbies[i])
            
            row = [
                str(i+1),
                str(name_val),
                str(smoothie_val),
                str(flower_val),
                str(animal_val),
                str(hobby_val)
            ]
            result["solution"]["rows"].append(row)
        
        # Output JSON
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()