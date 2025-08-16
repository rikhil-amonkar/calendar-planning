from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
heights = ["very tall", "tall", "very short", "average", "short"]
foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}
food = {h: String(f"food_{h}") for h in houses}

# Add constraints that each attribute is unique within its category
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([hobby[h] == ho for ho in hobbies]))
    s.add(Or([height[h] == he for he in heights]))
    s.add(Or([food[h] == f for f in foods]))

for i in range(len(names)):
    for j in range(i + 1, len(houses)):
        s.add(name[houses[i]] != name[houses[j]])
        s.add(hobby[houses[i]] != hobby[houses[j]])
        s.add(height[houses[i]] != height[houses[j]])
        s.add(food[houses[i]] != food[houses[j]])

# Clue 1: Bob is the photography enthusiast.
s.add(Or([And(name[h] == "Bob", hobby[h] == "photography") for h in houses]))

# Clue 2: The person who loves eating grilled cheese is the person who is tall.
s.add(Or([And(food[h] == "grilled cheese", height[h] == "tall") for h in houses]))

# Clue 3: Peter is not in the second house.
s.add(name[2] != "Peter")

# Clue 4: The person who is tall is directly left of the person who loves stir fry.
for h in range(1, 5):
    s.add(Implies(height[h] == "tall", food[h + 1] == "stir fry"))

# Clue 5: The person who loves cooking is the person who has an average height.
s.add(Or([And(hobby[h] == "cooking", height[h] == "average") for h in houses]))

# Clue 6: Alice is directly left of the person who is a pizza lover.
for h in range(1, 5):
    s.add(Implies(name[h] == "Alice", food[h + 1] == "pizza"))

# Clue 7: The person who loves the spaghetti eater is not in the second house.
s.add(food[2] != "spaghetti")

# Clue 8: Eric is not in the fifth house.
s.add(name[5] != "Eric")

# Clue 9: The person who is short is Peter.
s.add(Or([And(height[h] == "short", name[h] == "Peter") for h in houses]))

# Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
for h in range(1, 5):
    s.add(Or(
        And(height[h] == "average", hobby[h + 1] == "gardening"),
        And(height[h + 1] == "average", hobby[h] == "gardening")
    ))

# Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
for h in range(1, 5):
    s.add(Implies(hobby[h] == "painting", food[h + 1] == "grilled cheese"))

# Clue 12: The person who is very short is in the fifth house.
s.add(height[5] == "very short")

# Clue 13: The person who is tall is in the third house.
s.add(height[3] == "tall")

# Clue 14: Alice is somewhere to the right of the photography enthusiast.
# This means the house number of Alice is greater than the house number of the photography enthusiast.
photography_house = Int("photography_house")
alice_house = Int("alice_house")
s.add(Or([And(hobby[h] == "photography", photography_house == h) for h in houses]))
s.add(Or([And(name[h] == "Alice", alice_house == h) for h in houses]))
s.add(alice_house > photography_house)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(hobby[h]).as_string(),
            model.eval(height[h]).as_string(),
            model.eval(food[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")