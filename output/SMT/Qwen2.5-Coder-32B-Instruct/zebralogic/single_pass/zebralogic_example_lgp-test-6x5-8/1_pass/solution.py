from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
favorite_sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

# Create dictionaries to hold the variables
name_vars = {house: Int(f"name_{house}") for house in houses}
animal_vars = {house: Int(f"animal_{house}") for house in houses}
occupation_vars = {house: Int(f"occupation_{house}") for house in houses}
favorite_sport_vars = {house: Int(f"sport_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}

# Add constraints for unique values in each category
for house in houses:
    solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
    solver.add(animal_vars[house] >= 0, animal_vars[house] < len(animals))
    solver.add(occupation_vars[house] >= 0, occupation_vars[house] < len(occupations))
    solver.add(favorite_sport_vars[house] >= 0, favorite_sport_vars[house] < len(favorite_sports))
    solver.add(height_vars[house] >= 0, height_vars[house] < len(heights))

# All values in each category must be unique
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([animal_vars[house] for house in houses]))
solver.add(Distinct([occupation_vars[house] for house in houses]))
solver.add(Distinct([favorite_sport_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))

# Clues
# 1. The person who is an engineer is the dog owner.
solver.add(And([If(occupation_vars[house] == occupations.index("engineer"), animal_vars[house] == animals.index("dog"), True) for house in houses]))

# 2. The person who has an average height is somewhere to the left of the person who is short.
solver.add(Or([And(height_vars[i] == heights.index("average"), height_vars[j] == heights.index("short")) for i in houses for j in houses if i < j]))

# 3. The person who has an average height is directly left of the rabbit owner.
solver.add(Or([And(height_vars[i] == heights.index("average"), animal_vars[i + 1] == animals.index("rabbit")) for i in houses if i < 6]))

# 4. The person who is tall is somewhere to the left of the person who is very short.
solver.add(Or([And(height_vars[i] == heights.index("tall"), height_vars[j] == heights.index("very short")) for i in houses for j in houses if i < j]))

# 5. Arnold is the cat lover.
solver.add(And([If(name_vars[house] == names.index("Arnold"), animal_vars[house] == animals.index("cat"), True) for house in houses]))

# 6. The person who keeps horses is the person who is a teacher.
solver.add(And([If(animal_vars[house] == animals.index("horse"), occupation_vars[house] == occupations.index("teacher"), True) for house in houses]))

# 7. Carol is the person who loves soccer.
solver.add(And([If(name_vars[house] == names.index("Carol"), favorite_sport_vars[house] == favorite_sports.index("soccer"), True) for house in houses]))

# 8. The person who is tall is the person who loves volleyball.
solver.add(And([If(height_vars[house] == heights.index("tall"), favorite_sport_vars[house] == favorite_sports.index("volleyball"), True) for house in houses]))

# 9. The person who is a lawyer is in the fifth house.
solver.add(occupation_vars[5] == occupations.index("lawyer"))

# 10. The person who loves tennis is the person who is a teacher.
solver.add(And([If(favorite_sport_vars[house] == favorite_sports.index("tennis"), occupation_vars[house] == occupations.index("teacher"), True) for house in houses]))

# 11. The person who has an average height is the person who loves swimming.
solver.add(And([If(height_vars[house] == heights.index("average"), favorite_sport_vars[house] == favorite_sports.index("swimming"), True) for house in houses]))

# 12. The person who loves baseball is directly left of the person who is an engineer.
solver.add(Or([And(favorite_sport_vars[i] == favorite_sports.index("baseball"), occupation_vars[i + 1] == occupations.index("engineer")) for i in houses if i < 6]))

# 13. Peter is the person who is a nurse.
solver.add(And([If(name_vars[house] == names.index("Peter"), occupation_vars[house] == occupations.index("nurse"), True) for house in houses]))

# 14. Bob is somewhere to the right of the person who is an artist.
solver.add(Or([And(name_vars[i] == names.index("artist"), name_vars[j] == names.index("Bob")) for i in houses for j in houses if i < j]))

# 15. The person who is a teacher is directly left of the person who loves soccer.
solver.add(Or([And(occupation_vars[i] == occupations.index("teacher"), favorite_sport_vars[i + 1] == favorite_sports.index("soccer")) for i in houses if i < 6]))

# 16. The rabbit owner is Alice.
solver.add(And([If(animal_vars[house] == animals.index("rabbit"), name_vars[house] == names.index("Alice"), True) for house in houses]))

# 17. The fish enthusiast is Carol.
solver.add(And([If(animal_vars[house] == animals.index("fish"), name_vars[house] == names.index("Carol"), True) for house in houses]))

# 18. The person who loves baseball is in the first house.
solver.add(favorite_sport_vars[1] == favorite_sports.index("baseball"))

# 19. The cat lover is somewhere to the right of the person who is very short.
solver.add(Or([And(animal_vars[i] == animals.index("cat"), height_vars[j] == heights.index("very short")) for i in houses for j in houses if i > j]))

# 20. The person who is super tall is in the fifth house.
solver.add(height_vars[5] == heights.index("super tall"))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        animal = animals[model[animal_vars[house]].as_long()]
        occupation = occupations[model[occupation_vars[house]].as_long()]
        favorite_sport = favorite_sports[model[favorite_sport_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        solution.append([str(house), name, animal, occupation, favorite_sport, height])
    
    # Print the solution in JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],' +
          f'"rows": {solution}' +
          '}' +
          '}')
else:
    print("No solution found")