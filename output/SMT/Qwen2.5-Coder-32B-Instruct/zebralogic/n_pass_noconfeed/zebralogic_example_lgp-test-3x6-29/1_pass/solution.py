from z3 import *

# Define the variables
names = ['Arnold', 'Peter', 'Eric']
animals = ['bird', 'horse', 'cat']
birthdays = ['jan', 'sept', 'april']
hobbies = ['photography', 'cooking', 'gardening']
drinks = ['milk', 'water', 'tea']
hair_colors = ['black', 'brown', 'blonde']

# Create a solver instance
solver = Solver()

# Create variables for each attribute
house_vars = [Int(f'house_{i}') for i in range(1, 4)]
name_vars = [String(f'name_{i}') for i in range(1, 4)]
animal_vars = [String(f'animal_{i}') for i in range(1, 4)]
birthday_vars = [String(f'birthday_{i}') for i in range(1, 4)]
hobby_vars = [String(f'hobby_{i}') for i in range(1, 4)]
drink_vars = [String(f'drink_{i}') for i in range(1, 4)]
hair_color_vars = [String(f'hair_color_{i}') for i in range(1, 4)]

# Add constraints for unique values in each category
solver.add(Distinct(name_vars))
solver.add(Distinct(animal_vars))
solver.add(Distinct(birthday_vars))
solver.add(Distinct(hobby_vars))
solver.add(Distinct(drink_vars))
solver.add(Distinct(hair_color_vars))

# Add constraints for house numbers
solver.add(house_vars[0] == 1)
solver.add(house_vars[1] == 2)
solver.add(house_vars[2] == 3)

# Add specific clues as constraints
# 1. The person who has brown hair is the person who loves cooking.
solver.add(Implies(hair_color_vars[i] == 'brown', hobby_vars[i] == 'cooking') for i in range(3))
solver.add(Implies(hobby_vars[i] == 'cooking', hair_color_vars[i] == 'brown') for i in range(3))

# 2. The person whose birthday is in April is in the third house.
solver.add(birthday_vars[2] == 'april')

# 3. Eric is not in the first house.
solver.add(name_vars[0] != 'Eric')

# 4. The cat lover is in the second house.
solver.add(animal_vars[1] == 'cat')

# 5. The person who has blonde hair is somewhere to the left of the person who likes milk.
solver.add(Or(And(hair_color_vars[0] == 'blonde', drink_vars[1] == 'milk'), And(hair_color_vars[0] == 'blonde', drink_vars[2] == 'milk'), And(hair_color_vars[1] == 'blonde', drink_vars[2] == 'milk')))

# 6. The person who enjoys gardening is the person who likes milk.
solver.add(Implies(hobby_vars[i] == 'gardening', drink_vars[i] == 'milk') for i in range(3))
solver.add(Implies(drink_vars[i] == 'milk', hobby_vars[i] == 'gardening') for i in range(3))

# 7. The cat lover is the person who has brown hair.
solver.add(Implies(animal_vars[i] == 'cat', hair_color_vars[i] == 'brown') for i in range(3))
solver.add(Implies(hair_color_vars[i] == 'brown', animal_vars[i] == 'cat') for i in range(3))

# 8. Arnold is the bird keeper.
solver.add(Implies(name_vars[i] == 'Arnold', animal_vars[i] == 'bird') for i in range(3))
solver.add(Implies(animal_vars[i] == 'bird', name_vars[i] == 'Arnold') for i in range(3))

# 9. The one who only drinks water is the photography enthusiast.
solver.add(Implies(drink_vars[i] == 'water', hobby_vars[i] == 'photography') for i in range(3))
solver.add(Implies(hobby_vars[i] == 'photography', drink_vars[i] == 'water') for i in range(3))

# 10. The person whose birthday is in September is directly left of Arnold.
solver.add(Implies(birthday_vars[i] == 'sept', And(i < 2, name_vars[i + 1] == 'Arnold')) for i in range(2))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": []
        }
    }
    for i in range(3):
        house = str(model.eval(house_vars[i]).as_long())
        name = model.eval(name_vars[i]).as_string()[1:-1]
        animal = model.eval(animal_vars[i]).as_string()[1:-1]
        birthday = model.eval(birthday_vars[i]).as_string()[1:-1]
        hobby = model.eval(hobby_vars[i]).as_string()[1:-1]
        drink = model.eval(drink_vars[i]).as_string()[1:-1]
        hair_color = model.eval(hair_color_vars[i]).as_string()[1:-1]
        solution["solution"]["rows"].append([house, name, animal, birthday, hobby, drink, hair_color])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")