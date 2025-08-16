import json
from z3 import *

def solve_puzzle():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    house_styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    # Create variables for each attribute in each house
    name = {house: Int(f'name_{house}') for house in houses}
    house_style = {house: Int(f'house_style_{house}') for house in houses}
    food = {house: Int(f'food_{house}') for house in houses}
    vacation = {house: Int(f'vacation_{house}') for house in houses}
    height = {house: Int(f'height_{house}') for house in houses}
    cigar = {house: Int(f'cigar_{house}') for house in houses}

    # Add constraints to ensure each attribute is unique within its category
    for attr in [name, house_style, food, vacation, height, cigar]:
        s.add(Distinct([attr[house] for house in houses]))

    # Map each attribute to its possible values (0 to n-1)
    for house in houses:
        s.add(name[house] >= 0, name[house] < len(names))
        s.add(house_style[house] >= 0, house_style[house] < len(house_styles))
        s.add(food[house] >= 0, food[house] < len(foods))
        s.add(vacation[house] >= 0, vacation[house] < len(vacations))
        s.add(height[house] >= 0, height[house] < len(heights))
        s.add(cigar[house] >= 0, cigar[house] < len(cigars))

    # Clue 1: Alice is in the fifth house.
    s.add(name[5] == names.index('Alice'))

    # Clue 2: The person who loves stir fry is the person living in a colonial-style house.
    for house in houses:
        s.add(Implies(food[house] == foods.index('stir fry'), house_style[house] == house_styles.index('colonial'))

    # Clue 3: Alice is the person who loves the spaghetti eater.
    s.add(food[5] == foods.index('spaghetti'))

    # Clue 4: Arnold is the person who loves the stew.
    for house in houses:
        s.add(Implies(name[house] == names.index('Arnold'), food[house] == foods.index('stew')))

    # Clue 5: There is one house between the person who has an average height and Peter.
    for house in houses:
        if house + 2 <= 6:
            s.add(Implies(height[house] == heights.index('average'), name[house + 2] == names.index('Peter')))
        if house - 2 >= 1:
            s.add(Implies(height[house] == heights.index('average'), name[house - 2] == names.index('Peter')))

    # Clue 6: The person in a Craftsman-style house is not in the third house.
    s.add(house_style[3] != house_styles.index('craftsman'))

    # Clue 7: The person who has an average height is the person who loves stir fry.
    for house in houses:
        s.add(Implies(height[house] == heights.index('average'), food[house] == foods.index('stir fry')))

    # Clue 8: The person who loves beach vacations is the person in a ranch-style home.
    for house in houses:
        s.add(Implies(vacation[house] == vacations.index('beach'), house_style[house] == house_styles.index('ranch')))

    # Clue 9: Eric is in the fourth house.
    s.add(name[4] == names.index('Eric'))

    # Clue 10: There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
    for house in houses:
        if house + 2 <= 6:
            s.add(Implies(house_style[house] == house_styles.index('colonial'), vacation[house + 2] == vacations.index('camping')))
        if house - 2 >= 1:
            s.add(Implies(house_style[house] == house_styles.index('colonial'), vacation[house - 2] == vacations.index('camping')))

    # Clue 11: The person who enjoys mountain retreats is the person who smokes Yellow Monster.
    for house in houses:
        s.add(Implies(vacation[house] == vacations.index('mountain'), cigar[house] == cigars.index('yellow monster')))

    # Clue 12: The person who enjoys mountain retreats is the person who is very tall.
    for house in houses:
        s.add(Implies(vacation[house] == vacations.index('mountain'), height[house] == heights.index('very tall')))

    # Clue 13: The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
    for house in houses:
        if house > 1:
            s.add(Implies(vacation[house] == vacations.index('mountain'), Or(cigar[house - 1] == cigars.index('dunhill'), cigar[house + 1] == cigars.index('dunhill')) if house < 6 else cigar[house - 1] == cigars.index('dunhill')))
        if house < 6:
            s.add(Implies(vacation[house] == vacations.index('mountain'), Or(cigar[house + 1] == cigars.index('dunhill'), cigar[house - 1] == cigars.index('dunhill')) if house > 1 else cigar[house + 1] == cigars.index('dunhill')))

    # Clue 14: The person who loves the spaghetti eater is the person residing in a Victorian house.
    s.add(house_style[5] == house_styles.index('victorian'))

    # Clue 15: The person who is tall is the person who loves beach vacations.
    for house in houses:
        s.add(Implies(height[house] == heights.index('tall'), vacation[house] == vacations.index('beach')))

    # Clue 16: The person who is tall is somewhere to the left of the person residing in a Victorian house.
    for house in houses:
        if house < 5:
            s.add(Implies(height[house] == heights.index('tall'), house_style[5] == house_styles.index('victorian')))

    # Clue 17: The person who loves stir fry is directly left of Bob.
    for house in houses:
        if house < 6:
            s.add(Implies(food[house] == foods.index('stir fry'), name[house + 1] == names.index('Bob')))

    # Clue 18: The person in a modern-style house is somewhere to the left of Alice.
    for house in houses:
        if house < 5:
            s.add(Implies(house_style[house] == house_styles.index('modern'), name[5] == names.index('Alice')))

    # Clue 19: The person in a Craftsman-style house is somewhere to the left of the person who is short.
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                s.add(Implies(And(house_style[house1] == house_styles.index('craftsman'), height[house2] == heights.index('short')), house1 < house2))

    # Clue 20: The person who loves stir fry is somewhere to the left of the Prince smoker.
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                s.add(Implies(And(food[house1] == foods.index('stir fry'), cigar[house2] == cigars.index('prince')), house1 < house2))

    # Clue 21: There are two houses between the person who loves eating grilled cheese and the person who is super tall.
    for house in houses:
        if house + 3 <= 6:
            s.add(Implies(food[house] == foods.index('grilled cheese'), height[house + 3] == heights.index('super tall')))
        if house - 3 >= 1:
            s.add(Implies(food[house] == foods.index('grilled cheese'), height[house - 3] == heights.index('super tall')))

    # Clue 22: The person in a ranch-style home is the person who smokes Blue Master.
    for house in houses:
        s.add(Implies(house_style[house] == house_styles.index('ranch'), cigar[house] == cigars.index('blue master')))

    # Clue 23: The person who smokes many unique blends is directly left of the person who smokes Blue Master.
    for house in houses:
        if house < 6:
            s.add(Implies(cigar[house] == cigars.index('blends'), cigar[house + 1] == cigars.index('blue master')))

    # Clue 24: The person who goes on cultural tours is the person who is a pizza lover.
    for house in houses:
        s.add(Implies(vacation[house] == vacations.index('cultural'), food[house] == foods.index('pizza')))

    # Clue 25: The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                s.add(Implies(And(food[house1] == foods.index('pizza'), vacation[house2] == vacations.index('cruise')), house1 < house2))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()

        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": []
            }
        }

        for house in houses:
            row = [str(house)]
            # Get the name
            name_val = model.evaluate(name[house])
            row.append(names[name_val.as_long()])
            # Get the house style
            style_val = model.evaluate(house_style[house])
            row.append(house_styles[style_val.as_long()])
            # Get the food
            food_val = model.evaluate(food[house])
            row.append(foods[food_val.as_long()])
            # Get the vacation
            vacation_val = model.evaluate(vacation[house])
            row.append(vacations[vacation_val.as_long()])
            # Get the height
            height_val = model.evaluate(height[house])
            row.append(heights[height_val.as_long()])
            # Get the cigar
            cigar_val = model.evaluate(cigar[house])
            row.append(cigars[cigar_val.as_long()])
            solution["solution"]["rows"].append(row)

        return json.dumps(solution)
    else:
        return json.dumps({"error": "No solution found"})

print(solve_puzzle())