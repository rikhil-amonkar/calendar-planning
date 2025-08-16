from z3 import *

# Create variables for each characteristic
names = ['Eric', 'Peter', 'Arnold']
smoothies = ['cherry', 'watermelon', 'desert']
flowers = ['carnations', 'lilies', 'daffodils']
animals = ['cat', 'horse', 'bird']
hobbies = ['photography', 'cooking', 'gardening']

# Create a solver instance
solver = Solver()

# Define variables
house_vars = [Int(f"house_{i}") for i in range(1, 4)]
name_vars = {name: Int(f"name_{name}") for name in names}
smoothie_vars = {smoothie: Int(f"smoothie_{smoothie}") for smoothie in smoothies}
flower_vars = {flower: Int(f"flower_{flower}") for flower in flowers}
animal_vars = {animal: Int(f"animal_{animal}") for animal in animals}
hobby_vars = {hobby: Int(f"hobby_{hobby}") for hobby in hobbies}

# Add constraints for unique assignments
solver.add(Distinct(house_vars))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(smoothie_vars.values()))
solver.add(Distinct(flower_vars.values()))
solver.add(Distinct(animal_vars.values()))
solver.add(Distinct(hobby_vars.values()))

# Add constraints based on clues
# Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
solver.add(Abs(animal_vars['horse'] - hobby_vars['photography']) == 1)

# Clue 2: The bird keeper is the person who likes Cherry smoothies.
solver.add(animal_vars['bird'] == smoothie_vars['cherry'])

# Clue 3: The person who loves cooking is the Desert smoothie lover.
solver.add(hobby_vars['cooking'] == smoothie_vars['desert'])

# Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
solver.add(hobby_vars['gardening'] == flower_vars['carnations'])

# Clue 5: The person who loves cooking is directly left of Peter.
solver.add(hobby_vars['cooking'] + 1 == name_vars['Peter'])

# Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
solver.add(flower_vars['daffodils'] == smoothie_vars['desert'])

# Clue 7: The Watermelon smoothie lover is the person who keeps horses.
solver.add(smoothie_vars['watermelon'] == animal_vars['horse'])

# Clue 8: The photography enthusiast is Eric.
solver.add(hobby_vars['photography'] == name_vars['Eric'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": []
        }
    }
    
    for house in range(1, 4):
        name = None
        smoothie = None
        flower = None
        animal = None
        hobby = None
        
        for n, var in name_vars.items():
            if model.evaluate(var) == house:
                name = n
                
        for s, var in smoothie_vars.items():
            if model.evaluate(var) == house:
                smoothie = s
                
        for f, var in flower_vars.items():
            if model.evaluate(var) == house:
                flower = f
                
        for a, var in animal_vars.items():
            if model.evaluate(var) == house:
                animal = a
                
        for h, var in hobby_vars.items():
            if model.evaluate(var) == house:
                hobby = h
                
        solution["solution"]["rows"].append([str(house), name, smoothie, flower, animal, hobby])
        
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")