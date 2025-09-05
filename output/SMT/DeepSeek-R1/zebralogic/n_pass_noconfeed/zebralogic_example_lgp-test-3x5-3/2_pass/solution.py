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
    for i in range(3):
        for j in range(3):
            if abs(i - j) == 1:
                solver.add(Implies(animals[i] == Animal.horse, hobbies[j] == Hobby.photography))
                solver.add(Implies(hobbies[i] == Hobby.photography, animals[j] == Animal.horse))

    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for i in range(3):
        solver.add(Implies(animals[i] == Animal.bird, smoothies[i] == Smoothie.cherry))
        solver.add(Implies(smoothies[i] == Smoothie.cherry, animals[i] == Animal.bird))

    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for i in range(3):
        solver.add(Implies(hobbies[i] == Hobby.cooking, smoothies[i] == Smoothie.desert))
        solver.add(Implies(smoothies[i] == Smoothie.desert, hobbies[i] == Hobby.cooking))

    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    for i in range(3):
        solver.add(Implies(hobbies[i] == Hobby.gardening, flowers[i] == Flower.carnations))
        solver.add(Implies(flowers[i] == Flower.carnations, hobbies[i] == Hobby.gardening))

    # Clue 5: The person who loves cooking is directly left of Peter.
    for i in range(2):  # Houses 1 and 2 can be left of someone
        solver.add(Implies(hobbies[i] == Hobby.cooking, names[i+1] == Name.Peter))

    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for i in range(3):
        solver.add(Implies(flowers[i] == Flower.daffodils, smoothies[i] == Smoothie.desert))
        solver.add(Implies(smoothies[i] == Smoothie.desert, flowers[i] == Flower.daffodils))

    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for i in range(3):
        solver.add(Implies(smoothies[i] == Smoothie.watermelon, animals[i] == Animal.horse))
        solver.add(Implies(animals[i] == Animal.horse, smoothies[i] == Smoothie.watermelon))

    # Clue 8: The photography enthusiast is Eric.
    for i in range(3):
        solver.add(Implies(hobbies[i] == Hobby.photography, names[i] == Name.Eric))

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house numbers to their attribute values
        result = []
        for i in range(3):
            name_val = model.eval(names[i])
            smoothie_val = model.eval(smoothies[i])
            flower_val = model.eval(flowers[i])
            animal_val = model.eval(animals[i])
            hobby_val = model.eval(hobbies[i])
            
            # Convert Z3 datatype to string
            name_str = str(name_val)
            smoothie_str = str(smoothie_val)
            flower_str = str(flower_val)
            animal_str = str(animal_val)
            hobby_str = str(hobby_val)
            
            result.append([str(i+1), name_str, smoothie_str, flower_str, animal_str, hobby_str])
        
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