import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']
    
    # Add variables for each attribute
    problem.addVariables(['name'], names)
    problem.addVariables(['hair_color'], hair_colors)
    problem.addVariables(['height'], heights)
    
    # Add AllDifferent constraints
    problem.addConstraint(AllDifferentConstraint(), ['name'])
    problem.addConstraint(AllDifferentConstraint(), ['hair_color'])
    problem.addConstraint(AllDifferentConstraint(), ['height'])
    
    # Clue 1: The person who has blonde hair is directly left of Bob.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
                         any(hair_colors[i] == 'blonde' and names[j] == 'Bob' and j == i + 1 
                             for i in range(5) for j in range(1, 6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 2: Alice is in the fourth house.
    problem.addConstraint(lambda name4: name4 == 'Alice', ['name4'])
    
    # Clue 3: The person who is short is Arnold.
    problem.addConstraint(lambda height1, height2, height3, height4, height5, height6, name1, name2, name3, name4, name5, name6: 
                         any(heights[i] == 'short' and names[j] == 'Arnold' and i == j 
                             for i in range(6) for j in range(6)), 
                         ['height1', 'height2', 'height3', 'height4', 'height5', 'height6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 4: The person who is tall is in the sixth house.
    problem.addConstraint(lambda height6: height6 == 'tall', ['height6'])
    
    # Clue 5: The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda hair4: hair4 != 'black', ['hair_color4'])
    
    # Clue 6: The person who has red hair is Eric.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
                         any(hair_colors[i] == 'red' and names[j] == 'Eric' and i == j 
                             for i in range(6) for j in range(6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    problem.addConstraint(lambda height1, height2, height3, height4, height5, height6: 
                         any(heights[i] == 'average' and any(heights[j] == 'super tall' for j in range(i+1, 6)) 
                             for i in range(5)), 
                         ['height1', 'height2', 'height3', 'height4', 'height5', 'height6'])
    
    # Clue 8: The person who has blonde hair is Carol.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
                         any(hair_colors[i] == 'blonde' and names[j] == 'Carol' and i == j 
                             for i in range(6) for j in range(6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6: 
                         any((hair_colors[i] == 'gray' and hair_colors[j] == 'red' and abs(i - j) == 2) or 
                             (hair_colors[i] == 'red' and hair_colors[j] == 'gray' and abs(i - j) == 2) 
                             for i in range(6) for j in range(6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6'])
    
    # Clue 10: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height5: height5 == 'very short', ['height5'])
    
    # Clue 11: Bob is the person who has brown hair.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6, name1, name2, name3, name4, name5, name6: 
                         any(hair_colors[i] == 'brown' and names[j] == 'Bob' and i == j 
                             for i in range(6) for j in range(6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 12: The person who has gray hair is in the third house.
    problem.addConstraint(lambda hair3: hair3 == 'gray', ['hair_color3'])
    
    # Clue 13: The person who has blonde hair is the person who is very tall.
    problem.addConstraint(lambda hair1, hair2, hair3, hair4, hair5, hair6, height1, height2, height3, height4, height5, height6: 
                         any(hair_colors[i] == 'blonde' and heights[j] == 'very tall' and i == j 
                             for i in range(6) for j in range(6)), 
                         ['hair_color1', 'hair_color2', 'hair_color3', 'hair_color4', 'hair_color5', 'hair_color6',
                          'height1', 'height2', 'height3', 'height4', 'height5', 'height6'])
    
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