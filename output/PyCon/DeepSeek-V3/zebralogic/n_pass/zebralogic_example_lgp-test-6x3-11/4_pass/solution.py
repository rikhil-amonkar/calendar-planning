import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name{house}', names)
        problem.addVariable(f'hair_color{house}', hair_colors)
        problem.addVariable(f'height{house}', heights)
    
    # Add AllDifferent constraints
    problem.addConstraint(AllDifferentConstraint(), [f'name{house}' for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'hair_color{house}' for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'height{house}' for house in houses])
    
    # Clue 1: The person who has blonde hair is directly left of Bob.
    for i in range(1, 6):
        problem.addConstraint(
            lambda hair_i, name_j: not (hair_i == 'blonde') or (name_j == 'Bob'),
            [f'hair_color{i}', f'name{i+1}']
        )
    
    # Clue 2: Alice is in the fourth house.
    problem.addConstraint(lambda name4: name4 == 'Alice', ['name4'])
    
    # Clue 3: The person who is short is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda height, name: not (height == 'short') or (name == 'Arnold'),
            [f'height{house}', f'name{house}']
        )
    
    # Clue 4: The person who is tall is in the sixth house.
    problem.addConstraint(lambda height6: height6 == 'tall', ['height6'])
    
    # Clue 5: The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda hair4: hair4 != 'black', ['hair_color4'])
    
    # Clue 6: The person who has red hair is Eric.
    for house in houses:
        problem.addConstraint(
            lambda hair, name: not (hair == 'red') or (name == 'Eric'),
            [f'hair_color{house}', f'name{house}']
        )
    
    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    def super_tall_right_of_average(*heights):
        avg_index = None
        super_tall_index = None
        for i, height in enumerate(heights, 1):
            if height == 'average':
                avg_index = i
            if height == 'super tall':
                super_tall_index = i
        return avg_index is not None and super_tall_index is not None and super_tall_index > avg_index
    
    problem.addConstraint(super_tall_right_of_average, [f'height{house}' for house in houses])
    
    # Clue 8: The person who has blonde hair is Carol.
    for house in houses:
        problem.addConstraint(
            lambda hair, name: not (hair == 'blonde') or (name == 'Carol'),
            [f'hair_color{house}', f'name{house}']
        )
    
    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    def gray_red_separated(h1, h2, h3, h4, h5, h6):
        hair_colors = [h1, h2, h3, h4, h5, h6]
        gray_positions = [i+1 for i, color in enumerate(hair_colors) if color == 'gray']
        red_positions = [i+1 for i, color in enumerate(hair_colors) if color == 'red']
        
        for gray in gray_positions:
            for red in red_positions:
                if abs(gray - red) == 2:
                    return True
        return False
    
    problem.addConstraint(gray_red_separated, [f'hair_color{house}' for house in houses])
    
    # Clue 10: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height5: height5 == 'very short', ['height5'])
    
    # Clue 11: Bob is the person who has brown hair.
    for house in houses:
        problem.addConstraint(
            lambda hair, name: not (name == 'Bob') or (hair == 'brown'),
            [f'hair_color{house}', f'name{house}']
        )
    
    # Clue 12: The person who has gray hair is in the third house.
    problem.addConstraint(lambda hair3: hair3 == 'gray', ['hair_color3'])
    
    # Clue 13: The person who has blonde hair is the person who is very tall.
    for house in houses:
        problem.addConstraint(
            lambda hair, height: not (hair == 'blonde') or (height == 'very tall'),
            [f'hair_color{house}', f'height{house}']
        )
    
    # Generate all possible solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HairColor", "Height"], "rows": []}}
    
    # Convert to the required format
    solution = solutions[0]
    rows = []
    
    for house in range(1, 7):
        name = solution[f'name{house}']
        hair_color = solution[f'hair_color{house}']
        height = solution[f'height{house}']
        rows.append([str(house), name, hair_color, height])
    
    return {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))