from z3 import Solver, Int, Distinct, Or, And, sat

# Initialize solver
s = Solver()

# Define the house indices
houses = [1, 2, 3, 4, 5]

# Define the attributes and their mappings to integers
names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
name_to_int = {n: i for i, n in enumerate(names)}
int_to_name = {i: n for n, i in name_to_int.items()}

hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
hobby_to_int = {h: i for i, h in enumerate(hobbies)}
int_to_hobby = {i: h for h, i in hobby_to_int.items()}

heights = ["very tall", "tall", "average", "short", "very short"]
height_to_int = {h: i for i, h in enumerate(heights)}
int_to_height = {i: h for h, i in height_to_int.items()}

foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]
food_to_int = {f: i for i, f in enumerate(foods)}
int_to_food = {i: f for f, i in food_to_int.items()}

# Create Z3 variables for each house and attribute
name_vars = [Int(f'name_{i}') for i in houses]
hobby_vars = [Int(f'hobby_{i}') for i in houses]
height_vars = [Int(f'height_{i}') for i in houses]
food_vars = [Int(f'food_{i}') for i in houses]

# Each attribute must be between 0 and 4 (inclusive)
for i in houses:
    s.add(name_vars[i-1] >= 0, name_vars[i-1] < 5)
    s.add(hobby_vars[i-1] >= 0, hobby_vars[i-1] < 5)
    s.add(height_vars[i-1] >= 0, height_vars[i-1] < 5)
    s.add(food_vars[i-1] >= 0, food_vars[i-1] < 5)

# Each attribute list must have distinct values
s.add(Distinct(name_vars))
s.add(Distinct(hobby_vars))
s.add(Distinct(height_vars))
s.add(Distinct(food_vars))

# Clue 1: Bob is the photography enthusiast.
s.add([(name_vars[i] == name_to_int["Bob"]) == (hobby_vars[i] == hobby_to_int["photography"]) for i in range(5)])

# Clue 2: The person who loves eating grilled cheese is the person who is tall.
s.add([(food_vars[i] == food_to_int["grilled cheese"]) == (height_vars[i] == height_to_int["tall"]) for i in range(5)])

# Clue 3: Peter is not in the second house.
s.add(name_vars[1] != name_to_int["Peter"])

# Clue 4: The person who is tall is directly left of the person who loves stir fry.
s.add(Or(
    And(height_vars[0] == height_to_int["tall"], food_vars[1] == food_to_int["stir fry"]),
    And(height_vars[1] == height_to_int["tall"], food_vars[2] == food_to_int["stir fry"]),
    And(height_vars[2] == height_to_int["tall"], food_vars[3] == food_to_int["stir fry"]),
    And(height_vars[3] == height_to_int["tall"], food_vars[4] == food_to_int["stir fry"])
))

# Clue 5: The person who loves cooking is the person who has an average height.
s.add([(hobby_vars[i] == hobby_to_int["cooking"]) == (height_vars[i] == height_to_int["average"]) for i in range(5)])

# Clue 6: Alice is directly left of the person who is a pizza lover.
s.add(Or(
    And(name_vars[0] == name_to_int["Alice"], food_vars[1] == food_to_int["pizza"]),
    And(name_vars[1] == name_to_int["Alice"], food_vars[2] == food_to_int["pizza"]),
    And(name_vars[2] == name_to_int["Alice"], food_vars[3] == food_to_int["pizza"]),
    And(name_vars[3] == name_to_int["Alice"], food_vars[4] == food_to_int["pizza"])
))

# Clue 7: The person who loves the spaghetti eater is not in the second house.
# Interpreted as: The person who eats spaghetti is not in the second house.
s.add(food_vars[1] != food_to_int["spaghetti"])

# Clue 8: Eric is not in the fifth house.
s.add(name_vars[4] != name_to_int["Eric"])

# Clue 9: The person who is short is Peter.
s.add([(height_vars[i] == height_to_int["short"]) == (name_vars[i] == name_to_int["Peter"]) for i in range(5)])

# Clue 10: The person with average height and the person who enjoys gardening are adjacent.
s.add(Or(
    And(height_vars[0] == height_to_int["average"], hobby_vars[1] == hobby_to_int["gardening"]),
    And(height_vars[1] == height_to_int["average"], Or(hobby_vars[0] == hobby_to_int["gardening"], hobby_vars[2] == hobby_to_int["gardening"])),
    And(height_vars[2] == height_to_int["average"], Or(hobby_vars[1] == hobby_to_int["gardening"], hobby_vars[3] == hobby_to_int["gardening"])),
    And(height_vars[3] == height_to_int["average"], Or(hobby_vars[2] == hobby_to_int["gardening"], hobby_vars[4] == hobby_to_int["gardening"])),
    And(height_vars[4] == height_to_int["average"], hobby_vars[3] == hobby_to_int["gardening"])
))

# Clue 11: The person who paints is directly left of the person who loves grilled cheese.
s.add(Or(
    And(hobby_vars[0] == hobby_to_int["painting"], food_vars[1] == food_to_int["grilled cheese"]),
    And(hobby_vars[1] == hobby_to_int["painting"], food_vars[2] == food_to_int["grilled cheese"]),
    And(hobby_vars[2] == hobby_to_int["painting"], food_vars[3] == food_to_int["grilled cheese"]),
    And(hobby_vars[3] == hobby_to_int["painting"], food_vars[4] == food_to_int["grilled cheese"])
))

# Clue 12: The person who is very short is in the fifth house.
s.add(height_vars[4] == height_to_int["very short"])

# Clue 13: The person who is tall is in the third house.
s.add(height_vars[2] == height_to_int["tall"])

# Clue 14: Alice is somewhere to the right of the photography enthusiast.
# Find the house index of Alice and the house index of the photography hobby
s.add(Or(
    And(hobby_vars[0] == hobby_to_int["photography"], name_vars[1] == name_to_int["Alice"], 1 > 0),
    And(hobby_vars[0] == hobby_to_int["photography"], name_vars[2] == name_to_int["Alice"], 2 > 0),
    And(hobby_vars[0] == hobby_to_int["photography"], name_vars[3] == name_to_int["Alice"], 3 > 0),
    And(hobby_vars[0] == hobby_to_int["photography"], name_vars[4] == name_to_int["Alice"], 4 > 0),
    And(hobby_vars[1] == hobby_to_int["photography"], name_vars[2] == name_to_int["Alice"], 2 > 1),
    And(hobby_vars[1] == hobby_to_int["photography"], name_vars[3] == name_to_int["Alice"], 3 > 1),
    And(hobby_vars[1] == hobby_to_int["photography"], name_vars[4] == name_to_int["Alice"], 4 > 1),
    And(hobby_vars[2] == hobby_to_int["photography"], name_vars[3] == name_to_int["Alice"], 3 > 2),
    And(hobby_vars[2] == hobby_to_int["photography"], name_vars[4] == name_to_int["Alice"], 4 > 2),
    And(hobby_vars[3] == hobby_to_int["photography"], name_vars[4] == name_to_int["Alice"], 4 > 3)
))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = []
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(name_vars[i]).as_long()
        hobby_val = model.eval(hobby_vars[i]).as_long()
        height_val = model.eval(height_vars[i]).as_long()
        food_val = model.eval(food_vars[i]).as_long()
        row = [
            str(house_num),
            int_to_name[name_val],
            int_to_hobby[hobby_val],
            int_to_height[height_val],
            int_to_food[food_val]
        ]
        solution.append(row)
    
    # Prepare the JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": solution
        }
    }
    import json
    print(json.dumps(output, indent=2))
else:
    print("No solution found")