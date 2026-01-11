from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each characteristic for each house
names = [Int(f"name_{i}") for i in range(1, 5)]
hobbies = [Int(f"hobby_{i}") for i in range(1, 5)]
birthdays = [Int(f"birthday_{i}") for i in range(1, 5)]
educations = [Int(f"education_{i}") for i in range(1, 5)]
smoothies = [Int(f"smoothie_{i}") for i in range(1, 5)]

# Define domains for each variable
name_domain = [1, 2, 3, 4]  # 1: Arnold, 2: Alice, 3: Eric, 4: Peter
hobby_domain = [1, 2, 3, 4]  # 1: Cooking, 2: Painting, 3: Photography, 4: Gardening
birthday_domain = [1, 2, 3, 4]  # 1: Jan, 2: Feb, 3: Sept, 4: April
education_domain = [1, 2, 3, 4]  # 1: Master, 2: Bachelor, 3: Associate, 4: High School
smoothie_domain = [1, 2, 3, 4]  # 1: Cherry, 2: Watermelon, 3: Desert, 4: Dragonfruit

# Add domain constraints
for var in names + hobbies + birthdays + educations + smoothies:
    solver.add(var >= 1)
    solver.add(var <= 4)

# Ensure all values are unique within their respective categories
solver.add(Distinct(names))
solver.add(Distinct(hobbies))
solver.add(Distinct(birthdays))
solver.add(Distinct(educations))
solver.add(Distinct(smoothies))

# Clue 1 & 3: Desert smoothie lover has a bachelor's degree and birthday in January
solver.add(smoothies[0] == 3)  # Desert smoothie is in house 1
solver.add(educations[0] == 2)  # Bachelor's degree is in house 1
solver.add(birthdays[0] == 1)  # Birthday in January is in house 1

# Clue 4: Person with a high school diploma is in the third house
solver.add(educations[2] == 4)  # High school diploma is in house 3

# Clue 5: Watermelon smoothie lover is not in the third house
solver.add(smoothies[2] != 2)  # Watermelon smoothie is not in house 3

# Clue 6: Arnold has an associate's degree
solver.add(names[i] == 1 for i, edu in enumerate(educations) if edu == 3)  # Arnold is associated with associate's degree

# Clue 7: Person with a master's degree is the painter
solver.add(hobbies[i] == 2 for i, edu in enumerate(educations) if edu == 1)  # Painter is associated with master's degree

# Clue 8: One house between Dragonfruit smoothie lover and person whose birthday is in September
solver.add(Or(
    And(smoothies[0] == 4, birthdays[2] == 3),  # Dragonfruit in house 1, Sept in house 3
    And(smoothies[1] == 4, birthdays[3] == 3),  # Dragonfruit in house 2, Sept in house 4
    And(smoothies[2] == 4, birthdays[0] == 3),  # Dragonfruit in house 3, Sept in house 1
    And(smoothies[3] == 4, birthdays[1] == 3)   # Dragonfruit in house 4, Sept in house 2
))

# Clue 9: Person with a high school diploma has a birthday in September
solver.add(birthdays[2] == 3)  # High school diploma is in house 3, so Sept is in house 3

# Clue 10: Alice loves cooking
solver.add(And(names[i] == 2, hobbies[i] == 1) for i in range(4))  # Alice (2) loves cooking (1)

# Clue 11: Person whose birthday is in April and person who enjoys gardening are next to each other
solver.add(Or(
    And(birthdays[0] == 4, hobbies[1] == 4),  # April in house 1, Gardening in house 2
    And(birthdays[1] == 4, hobbies[0] == 4),  # April in house 2, Gardening in house 1
    And(birthdays[1] == 4, hobbies[2] == 4),  # April in house 2, Gardening in house 3
    And(birthdays[2] == 4, hobbies[1] == 4),  # April in house 3, Gardening in house 2
    And(birthdays[2] == 4, hobbies[3] == 4),  # April in house 3, Gardening in house 4
    And(birthdays[3] == 4, hobbies[2] == 4)   # April in house 4, Gardening in house 3
))

# Clue 12: Painter's birthday is in February
solver.add(And(hobbies[i] == 2, birthdays[i] == 2) for i in range(4))  # Painter (2) has birthday in February (2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": []
        }
    }
    
    name_map = {1: "Arnold", 2: "Alice", 3: "Eric", 4: "Peter"}
    hobby_map = {1: "cooking", 2: "painting", 3: "photography", 4: "gardening"}
    birthday_map = {1: "jan", 2: "feb", 3: "sept", 4: "april"}
    education_map = {1: "master", 2: "bachelor", 3: "associate", 4: "high school"}
    smoothie_map = {1: "cherry", 2: "watermelon", 3: "desert", 4: "dragonfruit"}
    
    for house in range(1, 5):
        name_val = model.evaluate(names[house-1]).as_long()
        hobby_val = model.evaluate(hobbies[house-1]).as_long()
        birthday_val = model.evaluate(birthdays[house-1]).as_long()
        education_val = model.evaluate(educations[house-1]).as_long()
        smoothie_val = model.evaluate(smoothies[house-1]).as_long()
        
        solution["solution"]["rows"].append([
            str(house),
            name_map[name_val],
            hobby_map[hobby_val],
            birthday_map[birthday_val],
            education_map[education_val],
            smoothie_map[smoothie_val]
        ])
    
    print(solution)
else:
    print("No solution found")