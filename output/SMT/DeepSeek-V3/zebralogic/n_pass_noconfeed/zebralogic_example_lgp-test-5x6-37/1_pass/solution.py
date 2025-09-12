import z3
import json

def main():
    # Define the number of houses
    n = 5
    houses = list(range(1, n+1))
    
    # Create Z3 variables for each attribute
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    
    # Create Z3 variables for each attribute position
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    hobby_vars = [z3.Int(f'hobby_{i}') for i in houses]
    sport_vars = [z3.Int(f'sport_{i}') for i in houses]
    style_vars = [z3.Int(f'style_{i}') for i in houses]
    child_vars = [z3.Int(f'child_{i}') for i in houses]
    height_vars = [z3.Int(f'height_{i}') for i in houses]
    
    # Create solver
    solver = z3.Solver()
    
    # Each attribute variable must be between 0 and 4 (index of the attribute)
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < 5))
        solver.add(z3.And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < 5))
        solver.add(z3.And(sport_vars[i-1] >= 0, sport_vars[i-1] < 5))
        solver.add(z3.And(style_vars[i-1] >= 0, style_vars[i-1] < 5))
        solver.add(z3.And(child_vars[i-1] >= 0, child_vars[i-1] < 5))
        solver.add(z3.And(height_vars[i-1] >= 0, height_vars[i-1] < 5))
    
    # All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(sport_vars))
    solver.add(z3.Distinct(style_vars))
    solver.add(z3.Distinct(child_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Helper function to get the house index where an attribute has a specific value
    def get_house_index(attr_vars, value):
        return z3.If(attr_vars[0] == value, 1,
            z3.If(attr_vars[1] == value, 2,
            z3.If(attr_vars[2] == value, 3,
            z3.If(attr_vars[3] == value, 4, 5))))
    
    # Helper function for "next to" constraint
    def adjacent(a, b):
        return z3.Or(a == b - 1, a == b + 1)
    
    # Helper function for "left of" constraint
    def left_of(a, b):
        return a < b
    
    # Helper function for "directly left" constraint
    def directly_left(a, b):
        return a == b - 1
    
    # Clue 1: The person who has an average height is the person's child is named Meredith.
    # average height person has child Meredith
    avg_height_idx = heights.index('average')
    meredith_idx = children.index('Meredith')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(height_vars[i] == avg_height_idx, child_vars[i] == meredith_idx)))
    
    # Clue 2: The person who is tall is in the second house.
    tall_idx = heights.index('tall')
    solver.add(height_vars[1] == tall_idx)
    
    # Clue 3: Peter is directly left of the person residing in a Victorian house.
    peter_idx = names.index('Peter')
    victorian_idx = styles.index('victorian')
    peter_house = get_house_index(name_vars, peter_idx)
    victorian_house = get_house_index(style_vars, victorian_idx)
    solver.add(directly_left(peter_house, victorian_house))
    
    # Clue 4: Alice is the person who is tall.
    alice_idx = names.index('Alice')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(name_vars[i] == alice_idx, height_vars[i] == tall_idx)))
    
    # Clue 5: The person who loves baseball is the person who is very tall.
    baseball_idx = sports.index('baseball')
    very_tall_idx = heights.index('very tall')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(sport_vars[i] == baseball_idx, height_vars[i] == very_tall_idx)))
    
    # Clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
    timothy_idx = children.index('Timothy')
    meredith_house = get_house_index(child_vars, meredith_idx)
    timothy_house = get_house_index(child_vars, timothy_idx)
    solver.add(adjacent(meredith_house, timothy_house))
    
    # Clue 7: Bob is the person who paints as a hobby.
    bob_idx = names.index('Bob')
    painting_idx = hobbies.index('painting')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(name_vars[i] == bob_idx, hobby_vars[i] == painting_idx)))
    
    # Clue 8: The person who enjoys gardening is in the second house.
    gardening_idx = hobbies.index('gardening')
    solver.add(hobby_vars[1] == gardening_idx)
    
    # Clue 9: The person who is very short is somewhere to the right of Eric.
    very_short_idx = heights.index('very short')
    eric_idx = names.index('Eric')
    very_short_house = get_house_index(height_vars, very_short_idx)
    eric_house = get_house_index(name_vars, eric_idx)
    solver.add(left_of(eric_house, very_short_house))
    
    # Clue 10: The person who loves tennis is the person's child is named Samantha.
    tennis_idx = sports.index('tennis')
    samantha_idx = children.index('Samantha')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(sport_vars[i] == tennis_idx, child_vars[i] == samantha_idx)))
    
    # Clue 11: The person who loves soccer is not in the first house.
    soccer_idx = sports.index('soccer')
    solver.add(sport_vars[0] != soccer_idx)
    
    # Clue 12: The person's child is named Samantha is the person in a modern-style house.
    modern_idx = styles.index('modern')
    samantha_house = get_house_index(child_vars, samantha_idx)
    modern_house = get_house_index(style_vars, modern_idx)
    solver.add(samantha_house == modern_house)
    
    # Clue 13: The person in a Craftsman-style house is the person who has an average height.
    craftsman_idx = styles.index('craftsman')
    craftsman_house = get_house_index(style_vars, craftsman_idx)
    avg_height_house = get_house_index(height_vars, avg_height_idx)
    solver.add(craftsman_house == avg_height_house)
    
    # Clue 14: The person's child is named Fred is the person residing in a Victorian house.
    fred_idx = children.index('Fred')
    fred_house = get_house_index(child_vars, fred_idx)
    solver.add(fred_house == victorian_house)
    
    # Clue 15: The person who is short is the person who loves basketball.
    short_idx = heights.index('short')
    basketball_idx = sports.index('basketball')
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(height_vars[i] == short_idx, sport_vars[i] == basketball_idx)))
    
    # Clue 16: Peter is the person who is very tall.
    solver.add(z3.Exists([i for i in range(5)], 
                z3.And(name_vars[i] == peter_idx, height_vars[i] == very_tall_idx)))
    
    # Clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    ranch_idx = styles.index('ranch')
    cooking_idx = hobbies.index('cooking')
    ranch_house = get_house_index(style_vars, ranch_idx)
    cooking_house = get_house_index(hobby_vars, cooking_idx)
    solver.add(left_of(ranch_house, cooking_house))
    
    # Clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
    knitting_idx = hobbies.index('knitting')
    knitting_house = get_house_index(hobby_vars, knitting_idx)
    gardening_house = get_house_index(hobby_vars, gardening_idx)
    solver.add(adjacent(knitting_house, gardening_house))
    
    # Clue 19: The person in a modern-style house is the person who loves cooking.
    solver.add(modern_house == cooking_house)
    
    # Clue 20: The person residing in a Victorian house is in the fifth house.
    solver.add(style_vars[4] == victorian_idx)
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in houses:
            name_val = model.evaluate(name_vars[house-1]).as_long()
            hobby_val = model.evaluate(hobby_vars[house-1]).as_long()
            sport_val = model.evaluate(sport_vars[house-1]).as_long()
            style_val = model.evaluate(style_vars[house-1]).as_long()
            child_val = model.evaluate(child_vars[house-1]).as_long()
            height_val = model.evaluate(height_vars[house-1]).as_long()
            
            row = [
                str(house),
                names[name_val],
                hobbies[hobby_val],
                sports[sport_val],
                styles[style_val],
                children[child_val],
                heights[height_val]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()