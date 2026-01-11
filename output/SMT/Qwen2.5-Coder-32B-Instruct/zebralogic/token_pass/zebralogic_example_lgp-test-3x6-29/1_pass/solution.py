from z3 import *

# Create symbolic variables
names = ['Arnold', 'Peter', 'Eric']
animals = ['bird', 'horse', 'cat']
birthdays = ['jan', 'sept', 'april']
hobbies = ['photography', 'cooking', 'gardening']
drinks = ['milk', 'water', 'tea']
hair_colors = ['black', 'brown', 'blonde']

house1_name = String('house1_name')
house2_name = String('house2_name')
house3_name = String('house3_name')

house1_animal = String('house1_animal')
house2_animal = String('house2_animal')
house3_animal = String('house3_animal')

house1_birthday = String('house1_birthday')
house2_birthday = String('house2_birthday')
house3_birthday = String('house3_birthday')

house1_hobby = String('house1_hobby')
house2_hobby = String('house2_hobby')
house3_hobby = String('house3_hobby')

house1_drink = String('house1_drink')
house2_drink = String('house2_drink')
house3_drink = String('house3_drink')

house1_hair_color = String('house1_hair_color')
house2_hair_color = String('house2_hair_color')
house3_hair_color = String('house3_hair_color')

# Create solver instance
solver = Solver()

# Add constraints for each house
solver.add(Or(house1_name == 'Arnold', house1_name == 'Peter', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Peter', house2_name == 'Eric'))
solver.add(Or(house3_name == 'Arnold', house3_name == 'Peter', house3_name == 'Eric'))
solver.add(Distinct(house1_name, house2_name, house3_name))

solver.add(Or(house1_animal == 'bird', house1_animal == 'horse', house1_animal == 'cat'))
solver.add(Or(house2_animal == 'bird', house2_animal == 'horse', house2_animal == 'cat'))
solver.add(Or(house3_animal == 'bird', house3_animal == 'horse', house3_animal == 'cat'))
solver.add(Distinct(house1_animal, house2_animal, house3_animal))

solver.add(Or(house1_birthday == 'jan', house1_birthday == 'sept', house1_birthday == 'april'))
solver.add(Or(house2_birthday == 'jan', house2_birthday == 'sept', house2_birthday == 'april'))
solver.add(Or(house3_birthday == 'jan', house3_birthday == 'sept', house3_birthday == 'april'))
solver.add(Distinct(house1_birthday, house2_birthday, house3_birthday))

solver.add(Or(house1_hobby == 'photography', house1_hobby == 'cooking', house1_hobby == 'gardening'))
solver.add(Or(house2_hobby == 'photography', house2_hobby == 'cooking', house2_hobby == 'gardening'))
solver.add(Or(house3_hobby == 'photography', house3_hobby == 'cooking', house3_hobby == 'gardening'))
solver.add(Distinct(house1_hobby, house2_hobby, house3_hobby))

solver.add(Or(house1_drink == 'milk', house1_drink == 'water', house1_drink == 'tea'))
solver.add(Or(house2_drink == 'milk', house2_drink == 'water', house2_drink == 'tea'))
solver.add(Or(house3_drink == 'milk', house3_drink == 'water', house3_drink == 'tea'))
solver.add(Distinct(house1_drink, house2_drink, house3_drink))

solver.add(Or(house1_hair_color == 'black', house1_hair_color == 'brown', house1_hair_color == 'blonde'))
solver.add(Or(house2_hair_color == 'black', house2_hair_color == 'brown', house2_hair_color == 'blonde'))
solver.add(Or(house3_hair_color == 'black', house3_hair_color == 'brown', house3_hair_color == 'blonde'))
solver.add(Distinct(house1_hair_color, house2_hair_color, house3_hair_color))

# Apply Clues
# Clue 1
solver.add(Implies(house1_hair_color == 'brown', house1_hobby == 'cooking'))
solver.add(Implies(house2_hair_color == 'brown', house2_hobby == 'cooking'))
solver.add(Implies(house3_hair_color == 'brown', house3_hobby == 'cooking'))

# Clue 2
solver.add(house3_birthday == 'april')

# Clue 3
solver.add(house1_name != 'Eric')

# Clue 4
solver.add(house2_animal == 'cat')

# Clue 5
solver.add(Implies(house1_hair_color == 'blonde', house1_drink != 'milk'))
solver.add(Implies(house2_hair_color == 'blonde', house3_drink == 'milk'))

# Clue 6
solver.add(Implies(house1_hobby == 'gardening', house1_drink == 'milk'))
solver.add(Implies(house2_hobby == 'gardening', house2_drink == 'milk'))
solver.add(Implies(house3_hobby == 'gardening', house3_drink == 'milk'))

# Clue 7
solver.add(Implies(house1_animal == 'cat', house1_hair_color == 'brown'))
solver.add(Implies(house2_animal == 'cat', house2_hair_color == 'brown'))
solver.add(Implies(house3_animal == 'cat', house3_hair_color == 'brown'))

# Clue 8
solver.add(house1_animal == 'bird' | house2_animal == 'bird' | house3_animal == 'bird')
solver.add(Implies(house1_animal == 'bird', house1_name == 'Arnold'))
solver.add(Implies(house2_animal == 'bird', house2_name == 'Arnold'))
solver.add(Implies(house3_animal == 'bird', house3_name == 'Arnold'))

# Clue 9
solver.add(Implies(house1_drink == 'water', house1_hobby == 'photography'))
solver.add(Implies(house2_drink == 'water', house2_hobby == 'photography'))
solver.add(Implies(house3_drink == 'water', house3_hobby == 'photography'))

# Clue 10
solver.add(Implies(house1_birthday == 'sept', house2_name == 'Arnold'))
solver.add(Implies(house2_birthday == 'sept', house3_name == 'Arnold'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": [
                ["1", model[house1_name].as_string(), model[house1_animal].as_string(), model[house1_birthday].as_string(), model[house1_hobby].as_string(), model[house1_drink].as_string(), model[house1_hair_color].as_string()],
                ["2", model[house2_name].as_string(), model[house2_animal].as_string(), model[house2_birthday].as_string(), model[house2_hobby].as_string(), model[house2_drink].as_string(), model[house2_hair_color].as_string()],
                ["3", model[house3_name].as_string(), model[house3_animal].as_string(), model[house3_birthday].as_string(), model[house3_hobby].as_string(), model[house3_drink].as_string(), model[house3_hair_color].as_string()]
            ]
        }
    }
    print(solution)
else:
    print("No solution found")