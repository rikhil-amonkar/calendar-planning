from z3 import *

def main():
    # Define enums for attributes
    NameSort, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    SmoothieSort, (cherry, watermelon, desert) = EnumSort('Smoothie', ['cherry', 'watermelon', 'desert'])
    FlowerSort, (carnations, lilies, daffodils) = EnumSort('Flower', ['carnations', 'lilies', 'daffodils'])
    AnimalSort, (cat, horse, bird) = EnumSort('Animal', ['cat', 'horse', 'bird'])
    HobbySort, (photography, cooking, gardening) = EnumSort('Hobby', ['photography', 'cooking', 'gardening'])
    
    # Houses: 0 -> House1, 1 -> House2, 2 -> House3
    n_houses = 3
    names = [Const(f'Name_{i}', NameSort) for i in range(n_houses)]
    smoothies = [Const(f'Smoothie_{i}', SmoothieSort) for i in range(n_houses)]
    flowers = [Const(f'Flower_{i}', FlowerSort) for i in range(n_houses)]
    animals = [Const(f'Animal_{i}', AnimalSort) for i in range(n_houses)]
    hobbies = [Const(f'Hobby_{i}', HobbySort) for i in range(n_houses)]
    
    s = Solver()
    
    # Uniqueness constraints
    s.add(Distinct(names[0], names[1], names[2]))
    s.add(Distinct(smoothies[0], smoothies[1], smoothies[2]))
    s.add(Distinct(flowers[0], flowers[1], flowers[2]))
    s.add(Distinct(animals[0], animals[1], animals[2]))
    s.add(Distinct(hobbies[0], hobbies[1], hobbies[2]))
    
    # Clue 1: The horse keeper and photography enthusiast are adjacent.
    s.add(Or(
        And(animals[0] == horse, hobbies[1] == photography),
        And(animals[1] == horse, hobbies[0] == photography),
        And(animals[1] == horse, hobbies[2] == photography),
        And(animals[2] == horse, hobbies[1] == photography)
    ))
    
    # Clue 2: The bird keeper is the cherry smoothie lover.
    for i in range(n_houses):
        s.add((animals[i] == bird) == (smoothies[i] == cherry))
    
    # Clue 3: The cooking enthusiast is the desert smoothie lover.
    for i in range(n_houses):
        s.add((hobbies[i] == cooking) == (smoothies[i] == desert))
    
    # Clue 4: The gardening enthusiast is the carnations lover.
    for i in range(n_houses):
        s.add((hobbies[i] == gardening) == (flowers[i] == carnations))
    
    # Clue 5: The cooking enthusiast is directly left of Peter.
    s.add(Or(
        And(hobbies[0] == cooking, names[1] == Peter),
        And(hobbies[1] == cooking, names[2] == Peter)
    ))
    
    # Clue 6: The daffodil lover is the desert smoothie lover.
    for i in range(n_houses):
        s.add((flowers[i] == daffodils) == (smoothies[i] == desert))
    
    # Clue 7: The watermelon smoothie lover is the horse keeper.
    for i in range(n_houses):
        s.add((smoothies[i] == watermelon) == (animals[i] == horse))
    
    # Clue 8: The photography enthusiast is Eric.
    for i in range(n_houses):
        s.add((hobbies[i] == photography) == (names[i] == Eric))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Dictionaries to map Z3 constants to strings
        name_dict = { Eric: "Eric", Peter: "Peter", Arnold: "Arnold" }
        smoothie_dict = { cherry: "cherry", watermelon: "watermelon", desert: "desert" }
        flower_dict = { carnations: "carnations", lilies: "lilies", daffodils: "daffodils" }
        animal_dict = { cat: "cat", horse: "horse", bird: "bird" }
        hobby_dict = { photography: "photography", cooking: "cooking", gardening: "gardening" }
        
        rows = []
        for i in range(n_houses):
            name_val = model.eval(names[i])
            smoothie_val = model.eval(smoothies[i])
            flower_val = model.eval(flowers[i])
            animal_val = model.eval(animals[i])
            hobby_val = model.eval(hobbies[i])
            row = [
                str(i+1),
                name_dict[name_val],
                smoothie_dict[smoothie_val],
                flower_dict[flower_val],
                animal_dict[animal_val],
                hobby_dict[hobby_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()