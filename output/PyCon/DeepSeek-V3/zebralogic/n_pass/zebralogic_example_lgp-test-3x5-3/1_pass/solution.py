import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'smoothie_{house}', smoothies)
        problem.addVariable(f'flower_{house}', flowers)
        problem.addVariable(f'animal_{house}', animals)
        problem.addVariable(f'hobby_{house}', hobbies)
    
    # All attributes must be unique across houses
    for attr in ['name', 'smoothie', 'flower', 'animal', 'hobby']:
        problem.addConstraint(AllDifferentConstraint(), [f'{attr}_{house}' for house in houses])
    
    # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
    def horse_photography_next(animal1, hobby1, animal2, hobby2, animal3, hobby3):
        positions = []
        horse_pos = None
        photo_pos = None
        
        if animal1 == 'horse': horse_pos = 1
        if animal2 == 'horse': horse_pos = 2
        if animal3 == 'horse': horse_pos = 3
        
        if hobby1 == 'photography': photo_pos = 1
        if hobby2 == 'photography': photo_pos = 2
        if hobby3 == 'photography': photo_pos = 3
        
        if horse_pos is not None and photo_pos is not None:
            return abs(horse_pos - photo_pos) == 1
        return False
    
    problem.addConstraint(horse_photography_next, 
                         ['animal_1', 'hobby_1', 'animal_2', 'hobby_2', 'animal_3', 'hobby_3'])
    
    # Clue 2: The bird keeper is the person who likes Cherry smoothies.
    for house in houses:
        problem.addConstraint(lambda animal, smoothie: not (animal == 'bird') or (smoothie == 'cherry'),
                             [f'animal_{house}', f'smoothie_{house}'])
    
    # Clue 3: The person who loves cooking is the Desert smoothie lover.
    for house in houses:
        problem.addConstraint(lambda hobby, smoothie: not (hobby == 'cooking') or (smoothie == 'desert'),
                             [f'hobby_{house}', f'smoothie_{house}'])
    
    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
    for house in houses:
        problem.addConstraint(lambda hobby, flower: not (hobby == 'gardening') or (flower == 'carnations'),
                             [f'hobby_{house}', f'flower_{house}'])
    
    # Clue 5: The person who loves cooking is directly left of Peter.
    def cooking_left_of_peter(hobby1, name1, hobby2, name2, hobby3, name3):
        cooking_pos = None
        peter_pos = None
        
        if hobby1 == 'cooking': cooking_pos = 1
        if hobby2 == 'cooking': cooking_pos = 2
        if hobby3 == 'cooking': cooking_pos = 3
        
        if name1 == 'Peter': peter_pos = 1
        if name2 == 'Peter': peter_pos = 2
        if name3 == 'Peter': peter_pos = 3
        
        if cooking_pos is not None and peter_pos is not None:
            return cooking_pos + 1 == peter_pos
        return False
    
    problem.addConstraint(cooking_left_of_peter,
                         ['hobby_1', 'name_1', 'hobby_2', 'name_2', 'hobby_3', 'name_3'])
    
    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
    for house in houses:
        problem.addConstraint(lambda flower, smoothie: not (flower == 'daffodils') or (smoothie == 'desert'),
                             [f'flower_{house}', f'smoothie_{house}'])
    
    # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
    for house in houses:
        problem.addConstraint(lambda smoothie, animal: not (smoothie == 'watermelon') or (animal == 'horse'),
                             [f'smoothie_{house}', f'animal_{house}'])
    
    # Clue 8: The photography enthusiast is Eric.
    for house in houses:
        problem.addConstraint(lambda hobby, name: not (hobby == 'photography') or (name == 'Eric'),
                             [f'hobby_{house}', f'name_{house}'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'smoothie_{house}'],
            solution[f'flower_{house}'],
            solution[f'animal_{house}'],
            solution[f'hobby_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))