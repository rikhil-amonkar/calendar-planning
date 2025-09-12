import json
from z3 import *

def main():
    # Define the possible values for each attribute
    name_values = ['Eric', 'Peter', 'Arnold']
    smoothie_values = ['cherry', 'watermelon', 'desert']
    flower_values = ['carnations', 'lilies', 'daffodils']
    animal_values = ['cat', 'horse', 'bird']
    hobby_values = ['photography', 'cooking', 'gardening']

    # Create Z3 variables for each house (0-based index: 0,1,2 for houses 1,2,3)
    names = [Int(f'name_{i}') for i in range(3)]
    smoothies = [Int(f'smoothie_{i}') for i in range(3)]
    flowers = [Int(f'flower_{i}') for i in range(3)]
    animals = [Int(f'animal_{i}') for i in range(3)]
    hobbies = [Int(f'hobby_{i}') for i in range(3)]

    s = Solver()

    # Add constraints for uniqueness and domain for each attribute
    for attr in [names, smoothies, flowers, animals, hobbies]:
        s.add(Distinct(attr))
        for var in attr:
            s.add(And(0 <= var, var <= 2))

    # Add constraints for each clue
    # Clue 1: Horse keeper and photography enthusiast are adjacent
    s.add(Or(
        And(animals[0] == 1, hobbies[1] == 0),
        And(animals[1] == 1, hobbies[0] == 0),
        And(animals[1] == 1, hobbies[2] == 0),
        And(animals[2] == 1, hobbies[1] == 0)
    ))

    # Clue 2: Bird keeper likes cherry smoothie
    s.add(Or(
        And(animals[0] == 2, smoothies[0] == 0),
        And(animals[1] == 2, smoothies[1] == 0),
        And(animals[2] == 2, smoothies[2] == 0)
    ))

    # Clue 3: Cooking lover is desert smoothie lover
    s.add(Or(
        And(hobbies[0] == 1, smoothies[0] == 2),
        And(hobbies[1] == 1, smoothies[1] == 2),
        And(hobbies[2] == 1, smoothies[2] == 2)
    ))

    # Clue 4: Gardening lover likes carnations
    s.add(Or(
        And(hobbies[0] == 2, flowers[0] == 0),
        And(hobbies[1] == 2, flowers[1] == 0),
        And(hobbies[2] == 2, flowers[2] == 0)
    ))

    # Clue 5: Cooking lover is directly left of Peter
    s.add(Or(
        And(hobbies[0] == 1, names[1] == 1),
        And(hobbies[1] == 1, names[2] == 1)
    ))

    # Clue 6: Daffodils lover is desert smoothie lover
    s.add(Or(
        And(flowers[0] == 2, smoothies[0] == 2),
        And(flowers[1] == 2, smoothies[1] == 2),
        And(flowers[2] == 2, smoothies[2] == 2)
    ))

    # Clue 7: Watermelon lover keeps horses
    s.add(Or(
        And(smoothies[0] == 1, animals[0] == 1),
        And(smoothies[1] == 1, animals[1] == 1),
        And(smoothies[2] == 1, animals[2] == 1)
    ))

    # Clue 8: Photography enthusiast is Eric
    s.add(Or(
        And(hobbies[0] == 0, names[0] == 0),
        And(hobbies[1] == 0, names[1] == 0),
        And(hobbies[2] == 0, names[2] == 0)
    ))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(3):
            house_num = i + 1
            name = name_values[model.evaluate(names[i]).as_long()]
            smoothie = smoothie_values[model.evaluate(smoothies[i]).as_long()]
            flower = flower_values[model.evaluate(flowers[i]).as_long()]
            animal = animal_values[model.evaluate(animals[i]).as_long()]
            hobby = hobby_values[model.evaluate(hobbies[i]).as_long()]
            rows.append([str(house_num), name, smoothie, flower, animal, hobby])
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()