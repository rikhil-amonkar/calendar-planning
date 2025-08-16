from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic of each person in each house
names = ['Arnold', 'Peter', 'Eric']
animals = ['bird', 'horse', 'cat']
birthdays = ['jan', 'sept', 'april']
hobbies = ['photography', 'cooking', 'gardening']
drinks = ['milk', 'water', 'tea']
hair_colors = ['black', 'brown', 'blonde']

# Create dictionaries to map each characteristic to a Z3 variable
house_vars = {i: {} for i in range(1, 4)}
for i in range(1, 4):
    house_vars[i]['name'] = EnumSort('name_' + str(i), names)[0]
    house_vars[i]['animal'] = EnumSort('animal_' + str(i), animals)[0]
    house_vars[i]['birthday'] = EnumSort('birthday_' + str(i), birthdays)[0]
    house_vars[i]['hobby'] = EnumSort('hobby_' + str(i), hobbies)[0]
    house_vars[i]['drink'] = EnumSort('drink_' + str(i), drinks)[0]
    house_vars[i]['hair_color'] = EnumSort('hair_color_' + str(i), hair_colors)[0]

# Uniqueness constraints for each characteristic across all houses
for char in ['name', 'animal', 'birthday', 'hobby', 'drink', 'hair_color']:
    solver.add(Distinct([house_vars[i][char] for i in range(1, 4)]))

# Clue 1: The person who has brown hair is the person who loves cooking.
solver.add(house_vars[1]['hair_color'] == 'brown') >> (house_vars[1]['hobby'] == 'cooking')
solver.add(house_vars[2]['hair_color'] == 'brown') >> (house_vars[2]['hobby'] == 'cooking')
solver.add(house_vars[3]['hair_color'] == 'brown') >> (house_vars[3]['hobby'] == 'cooking')

# Clue 2: The person whose birthday is in April is in the third house.
solver.add(house_vars[3]['birthday'] == 'april')

# Clue 3: Eric is not in the first house.
solver.add(house_vars[1]['name'] != 'Eric')

# Clue 4: The cat lover is in the second house.
solver.add(house_vars[2]['animal'] == 'cat')

# Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
solver.add((house_vars[1]['hair_color'] == 'blonde') | (house_vars[2]['hair_color'] == 'blonde'))
solver.add((house_vars[1]['hair_color'] == 'blonde') >> (house_vars[2]['drink'] != 'milk') & (house_vars[3]['drink'] != 'milk'))
solver.add((house_vars[2]['hair_color'] == 'blonde') >> (house_vars[3]['drink'] != 'milk'))

# Clue 6: The person who enjoys gardening is the person who likes milk.
solver.add(house_vars[1]['hobby'] == 'gardening') >> (house_vars[1]['drink'] == 'milk')
solver.add(house_vars[2]['hobby'] == 'gardening') >> (house_vars[2]['drink'] == 'milk')
solver.add(house_vars[3]['hobby'] == 'gardening') >> (house_vars[3]['drink'] == 'milk')

# Clue 7: The cat lover is the person who has brown hair.
solver.add(house_vars[2]['animal'] == 'cat') >> (house_vars[2]['hair_color'] == 'brown')

# Clue 8: Arnold is the bird keeper.
solver.add(house_vars[1]['name'] == 'Arnold') >> (house_vars[1]['animal'] == 'bird')
solver.add(house_vars[2]['name'] == 'Arnold') >> (house_vars[2]['animal'] == 'bird')
solver.add(house_vars[3]['name'] == 'Arnold') >> (house_vars[3]['animal'] == 'bird')

# Clue 9: The one who only drinks water is the photography enthusiast.
solver.add(house_vars[1]['drink'] == 'water') >> (house_vars[1]['hobby'] == 'photography')
solver.add(house_vars[2]['drink'] == 'water') >> (house_vars[2]['hobby'] == 'photography')
solver.add(house_vars[3]['drink'] == 'water') >> (house_vars[3]['hobby'] == 'photography')

# Clue 10: The person whose birthday is in September is directly left of Arnold.
solver.add(house_vars[1]['birthday'] == 'sept') >> (house_vars[2]['name'] == 'Arnold')
solver.add(house_vars[2]['birthday'] == 'sept') >> (house_vars[3]['name'] == 'Arnold')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": []
        }
    }
    for i in range(1, 4):
        house_solution = [str(i)]
        for char in ['name', 'animal', 'birthday', 'hobby', 'drink', 'hair_color']:
            var = house_vars[i][char]
            value = model.evaluate(var).as_string()[1:-1]  # Remove quotes from string representation
            house_solution.append(value)
        solution["solution"]["rows"].append(house_solution)

    print(solution)
else:
    print("No solution found")