from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each attribute
names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
favorite_sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
house_styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
heights = ["average", "very tall", "very short", "short", "tall"]

# Create dictionaries to map variables to Z3 variables
name_vars = {i: Int(f"name_{i}") for i in range(1, 6)}
hobby_vars = {i: Int(f"hobby_{i}") for i in range(1, 6)}
favorite_sport_vars = {i: Int(f"sport_{i}") for i in range(1, 6)}
house_style_vars = {i: Int(f"style_{i}") for i in range(1, 6)}
child_vars = {i: Int(f"child_{i}") for i in range(1, 6)}
height_vars = {i: Int(f"height_{i}") for i in range(1, 6)}

# Add constraints for each variable to be within the valid range
for i in range(1, 6):
    solver.add(name_vars[i] >= 0, name_vars[i] <= 4)
    solver.add(hobby_vars[i] >= 0, hobby_vars[i] <= 4)
    solver.add(favorite_sport_vars[i] >= 0, favorite_sport_vars[i] <= 4)
    solver.add(house_style_vars[i] >= 0, house_style_vars[i] <= 4)
    solver.add(child_vars[i] >= 0, child_vars[i] <= 4)
    solver.add(height_vars[i] >= 0, height_vars[i] <= 4)

# Ensure all values are unique within their categories
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(hobby_vars.values())))
solver.add(Distinct(list(favorite_sport_vars.values())))
solver.add(Distinct(list(house_style_vars.values())))
solver.add(Distinct(list(child_vars.values())))
solver.add(Distinct(list(height_vars.values())))

# Add constraints based on the clues
# Clue 1
solver.add(And(child_vars[4] == 3, height_vars[4] == 0))  # Meredith is average height, in Craftsman house

# Clue 2
solver.add(height_vars[2] == 4)  # Tall person in second house

# Clue 3
solver.add(name_vars[3] == 3)  # Peter is directly left of the person in Victorian house
solver.add(house_style_vars[4] == 3)  # Person in Victorian house in fourth house

# Clue 4
solver.add(And(name_vars[2] == 2, height_vars[2] == 4))  # Alice is tall, in second house

# Clue 5
solver.add(favorite_sport_vars[3] == 3)  # Person who loves baseball is very tall, Peter

# Clue 6
solver.add(Or(And(child_vars[3] == 0, child_vars[4] == 1), And(child_vars[4] == 0, child_vars[3] == 1)))  # Meredith and Timothy next to each other

# Clue 7
solver.add(hobby_vars[3] == 2)  # Bob is painter

# Clue 8
solver.add(hobby_vars[2] == 1)  # Gardener in second house

# Clue 9
solver.add(And(name_vars[5] != 4, name_vars[4] == 4))  # Very short is somewhere to the right of Eric

# Clue 10
solver.add(And(child_vars[5] == 1, favorite_sport_vars[5] == 1))  # Tennis player has child Samantha

# Clue 11
solver.add(favorite_sport_vars[1] != 2)  # Soccer player not in first house

# Clue 12
solver.add(And(child_vars[5] == 1, house_style_vars[5] == 3))  # Modern house has child Samantha

# Clue 13
solver.add(And(height_vars[4] == 0, house_style_vars[4] == 1))  # Average height in Craftsman house

# Clue 14
solver.add(And(child_vars[4] == 4, house_style_vars[4] == 3))  # Victorian house has child Fred

# Clue 15
solver.add(And(favorite_sport_vars[5] == 4, height_vars[5] == 3))  # Basketball player is short

# Clue 16
solver.add(height_vars[3] == 1)  # Peter is very tall

# Clue 17
solver.add(And(house_style_vars[1] == 0, house_style_vars[5] == 3))  # Ranch house left of cooking house

# Clue 18
solver.add(Or(And(hobby_vars[2] == 4, hobby_vars[3] == 1), And(hobby_vars[3] == 4, hobby_vars[2] == 1)))  # Knitter and Gardener next to each other

# Clue 19
solver.add(And(house_style_vars[5] == 3, hobby_vars[5] == 0))  # Modern house loves cooking

# Clue 20
solver.add(house_style_vars[5] == 3)  # Victorian house in fifth house

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(1, 6):
        name = names[model.evaluate(name_vars[i]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[i]).as_long()]
        sport = favorite_sports[model.evaluate(favorite_sport_vars[i]).as_long()]
        style = house_styles[model.evaluate(house_style_vars[i]).as_long()]
        child = children[model.evaluate(child_vars[i]).as_long()]
        height = heights[model.evaluate(height_vars[i]).as_long()]
        solution.append([str(i), name, hobby, sport, style, child, height])
    
    print({
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": solution
        }
    })
else:
    print("No solution found")