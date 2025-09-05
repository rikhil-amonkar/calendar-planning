import json
from z3 import *

def main():
    # Create solver
    solver = Solver()

    # Define enumerations for each attribute
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Arnold')
    Name = Name.create()

    Smoothie = Datatype('Smoothie')
    Smoothie.declare('cherry')
    Smoothie.declare('watermelon')
    Smoothie.declare('desert')
    Smoothie = Smoothie.create()

    Flower = Datatype('Flower')
    Flower.declare('carnations')
    Flower.declare('lilies')
    Flower.declare('daffodils')
    Flower = Flower.create()

    Animal = Datatype('Animal')
    Animal.declare('cat')
    Animal.declare('horse')
    Animal.declare('bird')
    Animal = Animal.create()

    Hobby = Datatype('Hobby')
    Hobby.declare('photography')
    Hobby.declare('cooking')
    Hobby.declare('gardening')
    Hobby = Hobby.create()

    # Create variables for each house and each attribute
    houses = [1, 2, 3]
    names = [Const(f'name_{i}', Name) for i in houses]
    smoothies = [Const(f'smoothie_{i}', Smoothie) for i in houses]
    flowers = [Const(f'flower_{i}', Flower) for i in houses]
    animals = [Const(f'animal_{i}', Animal) for i in houses]
    hobbies = [Const(f'hobby_{i}', Hobby) for i in houses]

    # Add constraint: all attributes are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(flowers))
    solver.add(Distinct(animals))
    solver.add(Distinct(hobbies))

    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    for i in houses:
        for j in houses:
            if abs(i - j) == 1:  # adjacent houses
                solver.add(Implies(animals[i-1] == Animal.horse, hobbies[j-1] == Hobby.photography))
                solver.add(Implies(hobbies[i-1] == Hobby.photography, animals[j-1] == Animal.horse))

    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for i in houses:
        solver.add(animals[i-1] == Animal.bird == smoothies[i-1] == Smoothie.cherry)

    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for i in houses:
        solver.add(hobbies[i-1] == Hobby.cooking == smoothies[i-1] == Smoothie.desert)

    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    for i in houses:
        solver.add(hobbies[i-1] == Hobby.gardening == flowers[i-1] == Flower.carnations)

    # Clue 5: The person who loves cooking is directly left of Peter.
    for i in [1, 2]:
        solver.add(Implies(hobbies[i-1] == Hobby.cooking, names[i] == Name.Peter))

    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for i in houses:
        solver.add(flowers[i-1] == Flower.daffodils == smoothies[i-1] == Smoothie.desert)

    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for i in houses:
        solver.add(smoothies[i-1] == Smoothie.watermelon == animals[i-1] == Animal.horse)

    # Clue 8: The photography enthusiast is Eric.
    for i in houses:
        solver.add(Implies(hobbies[i-1] == Hobby.photography, names[i-1] == Name.Eric))

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house numbers to their attribute values
        result = []
        for i in houses:
            name_val = model.eval(names[i-1])
            smoothie_val = model.eval(smoothies[i-1])
            flower_val = model.eval(flowers[i-1])
            animal_val = model.eval(animals[i-1])
            hobby_val = model.eval(hobbies[i-1])
            
            # Convert Z3 datatype to string
            name_str = str(name_val).split('!')[0]
            smoothie_str = str(smoothie_val).split('!')[0]
            flower_str = str(flower_val).split('!')[0]
            animal_str = str(animal_val).split('!')[0]
            hobby_str = str(hobby_val).split('!')[0]
            
            result.append([str(i), name_str, smoothie_str, flower_str, animal_str, hobby_str])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()