from z3 import *

# Define the variables
names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
house_styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
heights = ['average', 'very tall', 'very short', 'short', 'tall']

# Create the solver
solver = Solver()

# Create dictionaries for each attribute
name_vars = {i+1: Int(f'name_{i+1}') for i in range(5)}
hobby_vars = {i+1: Int(f'hobby_{i+1}') for i in range(5)}
sport_vars = {i+1: Int(f'sport_{i+1}') for i in range(5)}
house_style_vars = {i+1: Int(f'house_style_{i+1}') for i in range(5)}
child_vars = {i+1: Int(f'child_{i+1}') for i in range(5)}
height_vars = {i+1: Int(f'height_{i+1}') for i in range(5)}

# Add constraints for each attribute to be unique
solver.add(Distinct([name_vars[i] for i in range(1, 6)]))
solver.add(Distinct([hobby_vars[i] for i in range(1, 6)]))
solver.add(Distinct([sport_vars[i] for i in range(1, 6)]))
solver.add(Distinct([house_style_vars[i] for i in range(1, 6)]))
solver.add(Distinct([child_vars[i] for i in range(1, 6)]))
solver.add(Distinct([height_vars[i] for i in range(1, 6)]))

# Map the integer values to the actual strings
for i in range(1, 6):
    solver.add(Or([name_vars[i] == j for j in range(len(names))]))
    solver.add(Or([hobby_vars[i] == j for j in range(len(hobbies))]))
    solver.add(Or([sport_vars[i] == j for j in range(len(sports))]))
    solver.add(Or([house_style_vars[i] == j for j in range(len(house_styles))]))
    solver.add(Or([child_vars[i] == j for j in range(len(children))]))
    solver.add(Or([height_vars[i] == j for j in range(len(heights))]))

# Clue 1
solver.add(And(child_vars[i] == children.index('Meredith'), height_vars[i] == heights.index('average')) for i in range(1, 6))

# Clue 2
solver.add(height_vars[2] == heights.index('tall'))

# Clue 3
solver.add(And(name_vars[i] == names.index('Peter'), house_style_vars[i+1] == house_styles.index('victorian')) for i in range(1, 5))

# Clue 4
solver.add(height_vars[i] == heights.index('tall'), name_vars[i] == names.index('Alice')) for i in range(1, 6))

# Clue 5
solver.add(And(sport_vars[i] == sports.index('baseball'), height_vars[i] == heights.index('very tall')) for i in range(1, 6))

# Clue 6
solver.add(Or(And(child_vars[i] == children.index('Meredith'), child_vars[i+1] == children.index('Timothy')),
             And(child_vars[i+1] == children.index('Meredith'), child_vars[i] == children.index('Timothy')))
             for i in range(1, 5))

# Clue 7
solver.add(name_vars[i] == names.index('Bob'), hobby_vars[i] == hobbies.index('painting')) for i in range(1, 6))

# Clue 8
solver.add(hobby_vars[2] == hobbies.index('gardening'))

# Clue 9
solver.add(height_vars[i] == heights.index('very short'), child_vars[j] == children.index('Eric'))
             for i in range(1, 6) for j in range(i+1, 6))

# Clue 10
solver.add(And(child_vars[i] == children.index('Samantha'), sport_vars[i] == sports.index('tennis')) for i in range(1, 6))

# Clue 11
solver.add(sport_vars[i] != sports.index('soccer')) for i in [1])

# Clue 12
solver.add(And(child_vars[i] == children.index('Samantha'), house_style_vars[i] == house_styles.index('modern')) for i in range(1, 6))

# Clue 13
solver.add(And(height_vars[i] == heights.index('average'), house_style_vars[i] == house_styles.index('craftsman')) for i in range(1, 6))

# Clue 14
solver.add(And(child_vars[i] == children.index('Fred'), house_style_vars[i] == house_styles.index('victorian')) for i in range(1, 6))

# Clue 15
solver.add(And(sport_vars[i] == sports.index('basketball'), height_vars[i] == heights.index('short')) for i in range(1, 6))

# Clue 16
solver.add(name_vars[i] == names.index('Peter'), height_vars[i] == heights.index('very tall')) for i in range(1, 6))

# Clue 17
solver.add(And(house_style_vars[i] == house_styles.index('ranch'), hobby_vars[j] == hobbies.index('cooking'))
             for i in range(1, 5) for j in range(i+1, 6))

# Clue 18
solver.add(Or(And(hobby_vars[i] == hobbies.index('knitting'), hobby_vars[i+1] == hobbies.index('gardening')),
             And(hobby_vars[i+1] == hobbies.index('knitting'), hobby_vars[i] == hobbies.index('gardening')))
             for i in range(1, 5))

# Clue 19
solver.add(And(house_style_vars[i] == house_styles.index('modern'), hobby_vars[i] == hobbies.index('cooking')) for i in range(1, 6))

# Clue 20
solver.add(house_style_vars[5] == house_styles.index('victorian'))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": []
        }
    }
    for i in range(1, 6):
        name = names[model.evaluate(name_vars[i]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[i]).as_long()]
        sport = sports[model.evaluate(sport_vars[i]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[i]).as_long()]
        child = children[model.evaluate(child_vars[i]).as_long()]
        height = heights[model.evaluate(height_vars[i]).as_long()]
        solution["solution"]["rows"].append([str(i), name, hobby, sport, house_style, child, height])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")