import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    # Add variables for each attribute per house with proper naming
    for house in houses:
        problem.addVariable(f'name{house}', names)
        problem.addVariable(f'height{house}', heights)
        problem.addVariable(f'mother{house}', mothers)
        problem.addVariable(f'hair_color{house}', hair_colors)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f'name{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'height{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'mother{i}' for i in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'hair_color{i}' for i in houses])
    
    # Clue 1: The person who is tall is The person whose mother's name is Holly.
    for i in houses:
        problem.addConstraint(
            lambda height, mother: not (height == 'tall') or (mother == 'Holly'),
            (f'height{i}', f'mother{i}')
        )
        problem.addConstraint(
            lambda height, mother: not (mother == 'Holly') or (height == 'tall'),
            (f'height{i}', f'mother{i}')
        )
    
    # Clue 2: There are two houses between the person who has an average height and the person who is short.
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:
                problem.addConstraint(
                    lambda h1, h2: (h1 == 'average' and h2 == 'short') or (h1 == 'short' and h2 == 'average'),
                    (f'height{i}', f'height{j}')
                )
    
    # Clue 3: The person who has gray hair is directly left of The person whose mother's name is Janelle.
    for i in range(1, 5):
        problem.addConstraint(
            lambda hair, mother: (hair == 'gray') and (mother == 'Janelle'),
            (f'hair_color{i}', f'mother{i+1}')
        )
    
    # Clue 4: The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda hair: hair != 'black', ['hair_color4'])
    
    # Clue 5: Eric is the person who has black hair.
    for i in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Eric') or (hair == 'black'),
            (f'name{i}', f'hair_color{i}')
        )
        problem.addConstraint(
            lambda name, hair: not (hair == 'black') or (name == 'Eric'),
            (f'name{i}', f'hair_color{i}')
        )
    
    # Clue 6: The person who is very short is The person whose mother's name is Penny.
    for i in houses:
        problem.addConstraint(
            lambda height, mother: not (height == 'very short') or (mother == 'Penny'),
            (f'height{i}', f'mother{i}')
        )
        problem.addConstraint(
            lambda height, mother: not (mother == 'Penny') or (height == 'very short'),
            (f'height{i}', f'mother{i}')
        )
    
    # Clue 7: Eric and the person who has gray hair are next to each other.
    for i in houses:
        neighbors = []
        if i > 1:
            neighbors.append(i-1)
        if i < 5:
            neighbors.append(i+1)
        
        for neighbor in neighbors:
            problem.addConstraint(
                lambda name1, hair2: not (name1 == 'Eric') or (hair2 == 'gray'),
                (f'name{i}', f'hair_color{neighbor}')
            )
            problem.addConstraint(
                lambda hair1, name2: not (hair1 == 'gray') or (name2 == 'Eric'),
                (f'hair_color{i}', f'name{neighbor}')
            )
    
    # Clue 8: Bob is in the fifth house.
    problem.addConstraint(lambda name: name == 'Bob', ['name5'])
    
    # Clue 9: The person who has red hair is Peter.
    for i in houses:
        problem.addConstraint(
            lambda name, hair: not (hair == 'red') or (name == 'Peter'),
            (f'name{i}', f'hair_color{i}')
        )
        problem.addConstraint(
            lambda name, hair: not (name == 'Peter') or (hair == 'red'),
            (f'name{i}', f'hair_color{i}')
        )
    
    # Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
    for i in range(1, 5):
        problem.addConstraint(
            lambda mother, height: (mother == 'Kailyn') and (height == 'short'),
            (f'mother{i}', f'height{i+1}')
        )
    
    # Clue 11: Arnold is the person who has brown hair.
    for i in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Arnold') or (hair == 'brown'),
            (f'name{i}', f'hair_color{i}')
        )
        problem.addConstraint(
            lambda name, hair: not (hair == 'brown') or (name == 'Arnold'),
            (f'name{i}', f'hair_color{i}')
        )
    
    # Clue 12: The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
    for i in houses:
        for j in houses:
            if i >= j:
                problem.addConstraint(
                    lambda hair_i, mother_j: not (hair_i == 'brown' and mother_j == 'Janelle'),
                    (f'hair_color{i}', f'mother{j}')
                )
    
    # Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
    for i in houses:
        neighbors = []
        if i > 1:
            neighbors.append(i-1)
        if i < 5:
            neighbors.append(i+1)
        
        for neighbor in neighbors:
            problem.addConstraint(
                lambda mother1, height2: (mother1 == 'Aniya') and (height2 == 'very short'),
                (f'mother{i}', f'height{neighbor}')
            )
            problem.addConstraint(
                lambda height1, mother2: (height1 == 'very short') and (mother2 == 'Aniya'),
                (f'height{i}', f'mother{neighbor}')
            )
    
    # Clue 14: The person whose mother's name is Kailyn is in the third house.
    problem.addConstraint(lambda mother: mother == 'Kailyn', ['mother3'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height", "Mother", "HairColor"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        row = [
            str(house),
            solution[f'name{house}'],
            solution[f'height{house}'],
            solution[f'mother{house}'],
            solution[f'hair_color{house}']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))