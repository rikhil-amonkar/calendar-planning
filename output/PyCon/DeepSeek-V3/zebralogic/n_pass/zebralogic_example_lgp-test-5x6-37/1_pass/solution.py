import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    
    # Add variables for each attribute per house
    problem.addVariables(['name'] + names, houses)
    problem.addVariables(['hobby'] + hobbies, houses)
    problem.addVariables(['sport'] + sports, houses)
    problem.addVariables(['style'] + styles, houses)
    problem.addVariables(['child'] + children, houses)
    problem.addVariables(['height'] + heights, houses)
    
    # All attributes must have unique houses
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hobbies)
    problem.addConstraint(AllDifferentConstraint(), sports)
    problem.addConstraint(AllDifferentConstraint(), styles)
    problem.addConstraint(AllDifferentConstraint(), children)
    problem.addConstraint(AllDifferentConstraint(), heights)
    
    # Clue 1: The person who has an average height is the person's child is named Meredith.
    problem.addConstraint(lambda avg, mer: avg == mer, ['average', 'Meredith'])
    
    # Clue 2: The person who is tall is in the second house.
    problem.addConstraint(lambda tall: tall == 2, ['tall'])
    
    # Clue 3: Peter is directly left of the person residing in a Victorian house.
    problem.addConstraint(lambda peter, vict: peter + 1 == vict, ['Peter', 'victorian'])
    
    # Clue 4: Alice is the person who is tall.
    problem.addConstraint(lambda alice, tall: alice == tall, ['Alice', 'tall'])
    
    # Clue 5: The person who loves baseball is the person who is very tall.
    problem.addConstraint(lambda baseball, very_tall: baseball == very_tall, ['baseball', 'very tall'])
    
    # Clue 6: The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
    problem.addConstraint(lambda mer, tim: abs(mer - tim) == 1, ['Meredith', 'Timothy'])
    
    # Clue 7: Bob is the person who paints as a hobby.
    problem.addConstraint(lambda bob, paint: bob == paint, ['Bob', 'painting'])
    
    # Clue 8: The person who enjoys gardening is in the second house.
    problem.addConstraint(lambda garden: garden == 2, ['gardening'])
    
    # Clue 9: The person who is very short is somewhere to the right of Eric.
    problem.addConstraint(lambda very_short, eric: very_short > eric, ['very short', 'Eric'])
    
    # Clue 10: The person who loves tennis is the person's child is named Samantha.
    problem.addConstraint(lambda tennis, sam: tennis == sam, ['tennis', 'Samantha'])
    
    # Clue 11: The person who loves soccer is not in the first house.
    problem.addConstraint(lambda soccer: soccer != 1, ['soccer'])
    
    # Clue 12: The person's child is named Samantha is the person in a modern-style house.
    problem.addConstraint(lambda sam, modern: sam == modern, ['Samantha', 'modern'])
    
    # Clue 13: The person in a Craftsman-style house is the person who has an average height.
    problem.addConstraint(lambda crafts, avg: crafts == avg, ['craftsman', 'average'])
    
    # Clue 14: The person's child is named Fred is the person residing in a Victorian house.
    problem.addConstraint(lambda fred, vict: fred == vict, ['Fred', 'victorian'])
    
    # Clue 15: The person who is short is the person who loves basketball.
    problem.addConstraint(lambda short, basket: short == basket, ['short', 'basketball'])
    
    # Clue 16: Peter is the person who is very tall.
    problem.addConstraint(lambda peter, very_tall: peter == very_tall, ['Peter', 'very tall'])
    
    # Clue 17: The person in a ranch-style home is somewhere to the left of the person who loves cooking.
    problem.addConstraint(lambda ranch, cook: ranch < cook, ['ranch', 'cooking'])
    
    # Clue 18: The person who enjoys knitting and the person who enjoys gardening are next to each other.
    problem.addConstraint(lambda knit, garden: abs(knit - garden) == 1, ['knitting', 'gardening'])
    
    # Clue 19: The person in a modern-style house is the person who loves cooking.
    problem.addConstraint(lambda modern, cook: modern == cook, ['modern', 'cooking'])
    
    # Clue 20: The person residing in a Victorian house is in the fifth house.
    problem.addConstraint(lambda vict: vict == 5, ['victorian'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result table
    header = ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]
    rows = []
    
    for house in houses:
        row = [str(house)]
        
        # Find name for this house
        for name in names:
            if solution[name] == house:
                row.append(name)
                break
        
        # Find hobby for this house
        for hobby in hobbies:
            if solution[hobby] == house:
                row.append(hobby)
                break
        
        # Find sport for this house
        for sport in sports:
            if solution[sport] == house:
                row.append(sport)
                break
        
        # Find style for this house
        for style in styles:
            if solution[style] == house:
                row.append(style)
                break
        
        # Find child for this house
        for child in children:
            if solution[child] == house:
                row.append(child)
                break
        
        # Find height for this house
        for height in heights:
            if solution[height] == house:
                row.append(height)
                break
        
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))