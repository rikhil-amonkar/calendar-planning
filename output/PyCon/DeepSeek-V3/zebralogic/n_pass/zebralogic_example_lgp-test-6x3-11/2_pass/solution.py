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
            lambda hair_i, hair_j, name_i, name_j: not(hair_i == 'blonde' and name_j == 'Bob') or (hair_i == 'blonde' and name_j == 'Bob'),
            [f'hair_color{i}', f'hair_color{i+1}', f'name{i}', f'name{i+1}']
        )
    
    # Clue 2: Alice is in the fourth house.
    problem.addConstraint(lambda name4: name4 == 'Alice', ['name4'])
    
    # Clue 3: The person who is short is Arnold.
    problem.addConstraint(
        lambda height1, height2, height3, height4, height5, height6, name1, name2, name3, name4, name5, name6: 
        (height1 == 'short' and name1 == 'Arnold') or
        (height2 == 'short' and name2 == 'Arnold') or
        (height3 == 'short' and name3 == 'Arnold') or
        (height4 == 'short' and name4 == 'Arnold') or
        (height5 == 'short' and name5 == 'Arnold') or
        (height6 == 'short' and name6 == 'Arnold'),
        ['height1', 'height2', 'height3', 'height4', 'height5', 'height6',
         'name1', 'name2', 'name3', 'name4', 'name5', 'name6']
    )
    
    # Clue 4: The person who is tall is in the sixth house.
    problem.addConstraint(lambda height6: height6 == 'tall', ['height6'])
    
    # Clue 5: The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda hair4: hair4 != 'black', ['hair_color4'])
    
    # Clue 6: The person who has red hair is Eric.
    problem.addConstraint(
        lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
        (hair1 == 'red' and name1 == 'Eric') or
        (hair2 == 'red' and name2 == 'Eric') or
        (hair3 == 'red' and name3 == 'Eric') or
        (hair4 == 'red' and name4 == 'Eric') or
        (hair5 == 'red' and name5 == 'Eric') or
        (hair6 == 'red' and name6 == 'Eric'),
        ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
         'name1', 'name2', 'name3', 'name4', 'name5', 'name6']
    )
    
    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    problem.addConstraint(
        lambda height1, height2, height3, height4, height5, height6: 
        any(
            (height_i == 'average' and any(height_j == 'super tall' for j in range(i+1, 7)))
            for i in range(1, 7) for height_i in [eval(f'height{i}')]
        ),
        ['height1', 'height2', 'height3', 'height4', 'height5', 'height6']
    )
    
    # Clue 8: The person who has blonde hair is Carol.
    problem.addConstraint(
        lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
        (hair1 == 'blonde' and name1 == 'Carol') or
        (hair2 == 'blonde' and name2 == 'Carol') or
        (hair3 == 'blonde' and name3 == 'Carol') or
        (hair4 == 'blonde' and name4 == 'Carol') or
        (hair5 == 'blonde' and name5 == 'Carol') or
        (hair6 == 'blonde' and name6 == 'Carol'),
        ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
         'name1', 'name2', 'name3', 'name4', 'name5', 'name6']
    )
    
    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    problem.addConstraint(
        lambda hair1, hair2, hair3, hair4, hair5, hair6: 
        any(
            (eval(f'hair_color{i}') == 'gray' and eval(f'hair_color{j}') == 'red' and abs(i - j) == 2) or
            (eval(f'hair_color{i}') == 'red' and eval(f'hair_color{j}') == 'gray' and abs(i - j) == 2)
            for i in range(1, 7) for j in range(1, 7)
        ),
        ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6']
    )
    
    # Clue 10: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height5: height5 == 'very short', ['height5'])
    
    # Clue 11: Bob is the person who has brown hair.
    problem.addConstraint(
        lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
        (hair1 == 'brown' and name1 == 'Bob') or
        (hair2 == 'brown' and name2 == 'Bob') or
        (hair3 == 'brown' and name3 == 'Bob') or
        (hair4 == 'brown' and name4 == 'Bob') or
        (hair5 == 'brown' and name5 == 'Bob') or
        (hair6 == 'brown' and name6 == 'Bob'),
        ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
         'name1', 'name2', 'name3', 'name4', 'name5', 'name6']
    )
    
    # Clue 12: The person who has gray hair is in the third house.
    problem.addConstraint(lambda hair3: hair3 == 'gray', ['hair_color3'])
    
    # Clue 13: The person who has blonde hair is the person who is very tall.
    problem.addConstraint(
        lambda hair1, hair2, hair3, hair4, hair5, hair6, height1, height2, height3, height4, height5, height6: 
        (hair1 == 'blonde' and height1 == 'very tall') or
        (hair2 == 'blonde' and height2 == 'very tall') or
        (hair3 == 'blonde' and height3 == 'very tall') or
        (hair4 == 'blonde' and height4 == 'very tall') or
        (hair5 == 'blonde' and height5 == 'very tall') or
        (hair6 == 'blonde' and height6 == 'very tall'),
        ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
         'height1', 'height2', 'height3', 'height4', 'height5', 'height6']
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