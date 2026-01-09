import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    
    # Add variables for each house
    problem.addVariables(['name1', 'name2', 'name3', 'name4', 'name5'], names)
    problem.addVariables(['mother1', 'mother2', 'mother3', 'mother4', 'mother5'], mothers)
    problem.addVariables(['height1', 'height2', 'height3', 'height4', 'height5'], heights)
    
    # All attributes must be different within their category
    problem.addConstraint(AllDifferentConstraint(), ['name1', 'name2', 'name3', 'name4', 'name5'])
    problem.addConstraint(AllDifferentConstraint(), ['mother1', 'mother2', 'mother3', 'mother4', 'mother5'])
    problem.addConstraint(AllDifferentConstraint(), ['height1', 'height2', 'height3', 'height4', 'height5'])
    
    # Clue 1: Alice is The person whose mother's name is Aniya.
    for i in houses:
        problem.addConstraint(
            lambda name, mother, i=i: not (name == 'Alice' and mother != 'Aniya') and 
                                     not (mother == 'Aniya' and name != 'Alice'),
            [f'name{i}', f'mother{i}']
        )
    
    # Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    for i in houses:
        for j in houses:
            if j <= i:
                problem.addConstraint(
                    lambda height_i, mother_j, i=i, j=j: not (height_i == 'average' and mother_j == 'Penny'),
                    [f'height{i}', f'mother{j}']
                )
    
    # Clue 3: The person whose mother's name is Janelle is Bob.
    for i in houses:
        problem.addConstraint(
            lambda name, mother, i=i: not (mother == 'Janelle' and name != 'Bob') and 
                                     not (name == 'Bob' and mother != 'Janelle'),
            [f'name{i}', f'mother{i}']
        )
    
    # Clue 4: Peter is not in the second house.
    problem.addConstraint(lambda name: name != 'Peter', ['name2'])
    
    # Clue 5: The person who is short is directly left of Arnold.
    for i in range(1, 5):
        problem.addConstraint(
            lambda height_i, name_i1, i=i: not (height_i == 'short' and name_i1 != 'Arnold'),
            [f'height{i}', f'name{i+1}']
        )
    # Also ensure Arnold is not in house 1 if short is left of him
    problem.addConstraint(lambda name: name != 'Arnold', ['name1'])
    
    # Clue 6: The person who is very tall is Arnold.
    for i in houses:
        problem.addConstraint(
            lambda name, height, i=i: not (height == 'very tall' and name != 'Arnold') and 
                                     not (name == 'Arnold' and height != 'very tall'),
            [f'name{i}', f'height{i}']
        )
    
    # Clue 7: Bob is directly left of the person who has an average height.
    for i in range(1, 5):
        problem.addConstraint(
            lambda name_i, height_i1, i=i: not (name_i == 'Bob' and height_i1 != 'average'),
            [f'name{i}', f'height{i+1}']
        )
    # Also ensure average height is not in house 1 if Bob is left of it
    problem.addConstraint(lambda height: height != 'average', ['height1'])
    
    # Clue 8: Eric is not in the fifth house.
    problem.addConstraint(lambda name: name != 'Eric', ['name5'])
    
    # Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    for i in houses:
        for j in houses:
            if j >= i:
                problem.addConstraint(
                    lambda height_i, mother_j, i=i, j=j: not (height_i == 'very tall' and mother_j == 'Holly'),
                    [f'height{i}', f'mother{j}']
                )
    
    # Clue 10: Eric is The person whose mother's name is Kailyn.
    for i in houses:
        problem.addConstraint(
            lambda name, mother, i=i: not (name == 'Eric' and mother != 'Kailyn') and 
                                     not (mother == 'Kailyn' and name != 'Eric'),
            [f'name{i}', f'mother{i}']
        )
    
    # Clue 11: The person who is very short is in the fifth house.
    problem.addConstraint(lambda height: height == 'very short', ['height5'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Mother", "Height"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for i in houses:
        row = [
            str(i),
            solution[f'name{i}'],
            solution[f'mother{i}'],
            solution[f'height{i}']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))