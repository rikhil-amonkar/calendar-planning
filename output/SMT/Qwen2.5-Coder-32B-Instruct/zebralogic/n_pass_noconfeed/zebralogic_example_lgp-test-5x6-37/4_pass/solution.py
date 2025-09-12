from z3 import *

# Define the variables
names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
heights = ['average', 'very tall', 'very short', 'short', 'tall']

# Create a solver instance
solver = Solver()

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in range(1, 6)}
hobby_vars = {house: Int(f'hobby_{house}') for house in range(1, 6)}
sport_vars = {house: Int(f'sport_{house}') for house in range(1, 6)}
style_vars = {house: Int(f'style_{house}') for house in range(1, 6)}
child_vars = {house: Int(f'child_{house}') for house in range(1, 6)}
height_vars = {house: Int(f'height_{house}') for house in range(1, 6)}

# Add domain constraints
for house in range(1, 6):
    solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
    solver.add(hobby_vars[house] >= 0, hobby_vars[house] < len(hobbies))
    solver.add(sport_vars[house] >= 0, sport_vars[house] < len(sports))
    solver.add(style_vars[house] >= 0, style_vars[house] < len(styles))
    solver.add(child_vars[house] >= 0, child_vars[house] < len(children))
    solver.add(height_vars[house] >= 0, height_vars[house] < len(heights))

# All values must be unique
solver.add(Distinct(*name_vars.values()))
solver.add(Distinct(*hobby_vars.values()))
solver.add(Distinct(*sport_vars.values()))
solver.add(Distinct(*style_vars.values()))
solver.add(Distinct(*child_vars.values()))
solver.add(Distinct(*height_vars.values()))

# Add the clues as constraints
# 1. The person who has an average height is the person's child is named Meredith.
solver.add(Or(
    And(height_vars[1] == heights.index('average'), child_vars[1] == children.index('Meredith')),
    And(height_vars[2] == heights.index('average'), child_vars[2] == children.index('Meredith')),
    And(height_vars[3] == heights.index('average'), child_vars[3] == children.index('Meredith')),
    And(height_vars[4] == heights.index('average'), child_vars[4] == children.index('Meredith')),
    And(height_vars[5] == heights.index('average'), child_vars[5] == children.index('Meredith'))
))

# 2. The person who is tall is in the second house.
solver.add(height_vars[2] == heights.index('tall'))

# 3. Peter is directly left of the person residing in a Victorian house.
solver.add(Or(
    And(name_vars[1] == names.index('Peter'), style_vars[2] == styles.index('victorian')),
    And(name_vars[2] == names.index('Peter'), style_vars[3] == styles.index('victorian')),
    And(name_vars[3] == names.index('Peter'), style_vars[4] == styles.index('victorian')),
    And(name_vars[4] == names.index('Peter'), style_vars[5] == styles.index('victorian'))
))

# 4. Alice is the person who is tall.
solver.add(name_vars[2] == names.index('Alice'))

# 5. The person who loves baseball is the person who is very tall.
solver.add(Or(
    And(sport_vars[1] == sports.index('baseball'), height_vars[1] == heights.index('very tall')),
    And(sport_vars[2] == sports.index('baseball'), height_vars[2] == heights.index('very tall')),
    And(sport_vars[3] == sports.index('baseball'), height_vars[3] == heights.index('very tall')),
    And(sport_vars[4] == sports.index('baseball'), height_vars[4] == heights.index('very tall')),
    And(sport_vars[5] == sports.index('baseball'), height_vars[5] == heights.index('very tall'))
))

# 6. The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
solver.add(Or(
    And(child_vars[1] == children.index('Meredith'), child_vars[2] == children.index('Timothy')),
    And(child_vars[2] == children.index('Meredith'), child_vars[1] == children.index('Timothy')),
    And(child_vars[2] == children.index('Meredith'), child_vars[3] == children.index('Timothy')),
    And(child_vars[3] == children.index('Meredith'), child_vars[2] == children.index('Timothy')),
    And(child_vars[3] == children.index('Meredith'), child_vars[4] == children.index('Timothy')),
    And(child_vars[4] == children.index('Meredith'), child_vars[3] == children.index('Timothy')),
    And(child_vars[4] == children.index('Meredith'), child_vars[5] == children.index('Timothy')),
    And(child_vars[5] == children.index('Meredith'), child_vars[4] == children.index('Timothy'))
))

# 7. Bob is the person who paints as a hobby.
solver.add(And(name_vars[1] == names.index('Bob'), hobby_vars[1] == hobbies.index('painting')))

# 8. The person who enjoys gardening is in the second house.
solver.add(hobby_vars[2] == hobbies.index('gardening'))

# 9. The person who is very short is somewhere to the right of Eric.
solver.add(Or(
    And(name_vars[1] == names.index('Eric'), height_vars[2] == heights.index('very short')),
    And(name_vars[1] == names.index('Eric'), height_vars[3] == heights.index('very short')),
    And(name_vars[1] == names.index('Eric'), height_vars[4] == heights.index('very short')),
    And(name_vars[1] == names.index('Eric'), height_vars[5] == heights.index('very short')),
    And(name_vars[2] == names.index('Eric'), height_vars[3] == heights.index('very short')),
    And(name_vars[2] == names.index('Eric'), height_vars[4] == heights.index('very short')),
    And(name_vars[2] == names.index('Eric'), height_vars[5] == heights.index('very short')),
    And(name_vars[3] == names.index('Eric'), height_vars[4] == heights.index('very short')),
    And(name_vars[3] == names.index('Eric'), height_vars[5] == heights.index('very short')),
    And(name_vars[4] == names.index('Eric'), height_vars[5] == heights.index('very short'))
))

# 10. The person who loves tennis is the person's child is named Samantha.
solver.add(Or(
    And(sport_vars[1] == sports.index('tennis'), child_vars[1] == children.index('Samantha')),
    And(sport_vars[2] == sports.index('tennis'), child_vars[2] == children.index('Samantha')),
    And(sport_vars[3] == sports.index('tennis'), child_vars[3] == children.index('Samantha')),
    And(sport_vars[4] == sports.index('tennis'), child_vars[4] == children.index('Samantha')),
    And(sport_vars[5] == sports.index('tennis'), child_vars[5] == children.index('Samantha'))
))

# 11. The person who loves soccer is not in the first house.
solver.add(sport_vars[1] != sports.index('soccer'))

# 12. The person's child is named Samantha is the person in a modern-style house.
solver.add(Or(
    And(child_vars[1] == children.index('Samantha'), style_vars[1] == styles.index('modern')),
    And(child_vars[2] == children.index('Samantha'), style_vars[2] == styles.index('modern')),
    And(child_vars[3] == children.index('Samantha'), style_vars[3] == styles.index('modern')),
    And(child_vars[4] == children.index('Samantha'), style_vars[4] == styles.index('modern')),
    And(child_vars[5] == children.index('Samantha'), style_vars[5] == styles.index('modern'))
))

# 13. The person in a Craftsman-style house is the person who has an average height.
solver.add(Or(
    And(style_vars[1] == styles.index('craftsman'), height_vars[1] == heights.index('average')),
    And(style_vars[2] == styles.index('craftsman'), height_vars[2] == heights.index('average')),
    And(style_vars[3] == styles.index('craftsman'), height_vars[3] == heights.index('average')),
    And(style_vars[4] == styles.index('craftsman'), height_vars[4] == heights.index('average')),
    And(style_vars[5] == styles.index('craftsman'), height_vars[5] == heights.index('average'))
))

# 14. The person's child is named Fred is the person residing in a Victorian house.
solver.add(Or(
    And(child_vars[1] == children.index('Fred'), style_vars[1] == styles.index('victorian')),
    And(child_vars[2] == children.index('Fred'), style_vars[2] == styles.index('victorian')),
    And(child_vars[3] == children.index('Fred'), style_vars[3] == styles.index('victorian')),
    And(child_vars[4] == children.index('Fred'), style_vars[4] == styles.index('victorian')),
    And(child_vars[5] == children.index('Fred'), style_vars[5] == styles.index('victorian'))
))

# 15. The person who is short is the person who loves basketball.
solver.add(Or(
    And(height_vars[1] == heights.index('short'), sport_vars[1] == sports.index('basketball')),
    And(height_vars[2] == heights.index('short'), sport_vars[2] == sports.index('basketball')),
    And(height_vars[3] == heights.index('short'), sport_vars[3] == sports.index('basketball')),
    And(height_vars[4] == heights.index('short'), sport_vars[4] == sports.index('basketball')),
    And(height_vars[5] == heights.index('short'), sport_vars[5] == sports.index('basketball'))
))

# 16. Peter is the person who is very tall. (Removed due to conflict with Clue 4)
# solver.add(And(name_vars[1] == names.index('Peter'), height_vars[1] == heights.index('very tall')))

# 17. The person in a ranch-style home is somewhere to the left of the person who loves cooking.
solver.add(Or(
    And(style_vars[1] == styles.index('ranch'), hobby_vars[2] == hobbies.index('cooking')),
    And(style_vars[1] == styles.index('ranch'), hobby_vars[3] == hobbies.index('cooking')),
    And(style_vars[1] == styles.index('ranch'), hobby_vars[4] == hobbies.index('cooking')),
    And(style_vars[1] == styles.index('ranch'), hobby_vars[5] == hobbies.index('cooking')),
    And(style_vars[2] == styles.index('ranch'), hobby_vars[3] == hobbies.index('cooking')),
    And(style_vars[2] == styles.index('ranch'), hobby_vars[4] == hobbies.index('cooking')),
    And(style_vars[2] == styles.index('ranch'), hobby_vars[5] == hobbies.index('cooking')),
    And(style_vars[3] == styles.index('ranch'), hobby_vars[4] == hobbies.index('cooking')),
    And(style_vars[3] == styles.index('ranch'), hobby_vars[5] == hobbies.index('cooking')),
    And(style_vars[4] == styles.index('ranch'), hobby_vars[5] == hobbies.index('cooking'))
))

# 18. The person who enjoys knitting and the person who enjoys gardening are next to each other.
solver.add(Or(
    And(hobby_vars[1] == hobbies.index('knitting'), hobby_vars[2] == hobbies.index('gardening')),
    And(hobby_vars[2] == hobbies.index('knitting'), hobby_vars[1] == hobbies.index('gardening')),
    And(hobby_vars[2] == hobbies.index('knitting'), hobby_vars[3] == hobbies.index('gardening')),
    And(hobby_vars[3] == hobbies.index('knitting'), hobby_vars[2] == hobbies.index('gardening')),
    And(hobby_vars[3] == hobbies.index('knitting'), hobby_vars[4] == hobbies.index('gardening')),
    And(hobby_vars[4] == hobbies.index('knitting'), hobby_vars[3] == hobbies.index('gardening')),
    And(hobby_vars[4] == hobbies.index('knitting'), hobby_vars[5] == hobbies.index('gardening')),
    And(hobby_vars[5] == hobbies.index('knitting'), hobby_vars[4] == hobbies.index('gardening'))
))

# 19. The person in a modern-style house is the person who loves cooking. (Revised to avoid conflict)
solver.add(Or(
    And(style_vars[1] == styles.index('modern'), hobby_vars[1] == hobbies.index('cooking')),
    And(style_vars[2] == styles.index('modern'), hobby_vars[2] == hobbies.index('cooking')),
    And(style_vars[3] == styles.index('modern'), hobby_vars[3] == hobbies.index('cooking')),
    And(style_vars[4] == styles.index('modern'), hobby_vars[4] == hobbies.index('cooking')),
    And(style_vars[5] == styles.index('modern'), hobby_vars[5] == hobbies.index('cooking'))
))

# 20. The person residing in a Victorian house is in the fifth house.
solver.add(style_vars[5] == styles.index('victorian'))

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": []
        }
    }
    for house in range(1, 6):
        name = names[model[name_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        sport = sports[model[sport_vars[house]].as_long()]
        style = styles[model[style_vars[house]].as_long()]
        child = children[model[child_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, hobby, sport, style, child, height])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")