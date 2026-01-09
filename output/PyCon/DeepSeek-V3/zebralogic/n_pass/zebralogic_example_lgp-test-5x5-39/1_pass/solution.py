import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    birthdays = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']
    
    # Add variables for each attribute per house
    problem.addVariables(['name1', 'name2', 'name3', 'name4', 'name5'], names)
    problem.addVariables(['birthday1', 'birthday2', 'birthday3', 'birthday4', 'birthday5'], birthdays)
    problem.addVariables(['mother1', 'mother2', 'mother3', 'mother4', 'mother5'], mothers)
    problem.addVariables(['occupation1', 'occupation2', 'occupation3', 'occupation4', 'occupation5'], occupations)
    problem.addVariables(['hair1', 'hair2', 'hair3', 'hair4', 'hair5'], hair_colors)
    
    # All attributes must be different within their category
    problem.addConstraint(AllDifferentConstraint(), ['name1', 'name2', 'name3', 'name4', 'name5'])
    problem.addConstraint(AllDifferentConstraint(), ['birthday1', 'birthday2', 'birthday3', 'birthday4', 'birthday5'])
    problem.addConstraint(AllDifferentConstraint(), ['mother1', 'mother2', 'mother3', 'mother4', 'mother5'])
    problem.addConstraint(AllDifferentConstraint(), ['occupation1', 'occupation2', 'occupation3', 'occupation4', 'occupation5'])
    problem.addConstraint(AllDifferentConstraint(), ['hair1', 'hair2', 'hair3', 'hair4', 'hair5'])
    
    # Clue 1: The person whose birthday is in March is in the fifth house.
    problem.addConstraint(lambda b5: b5 == 'mar', ['birthday5'])
    
    # Clue 2: The person whose birthday is in February is in the first house.
    problem.addConstraint(lambda b1: b1 == 'feb', ['birthday1'])
    
    # Clue 3: The person who is a doctor is Eric.
    for i in range(1, 6):
        problem.addConstraint(lambda occ, name, i=i: not (occ == 'doctor') or (name == 'Eric'), 
                            [f'occupation{i}', f'name{i}'])
    
    # Clue 4: The person whose mother's name is Janelle is in the third house.
    problem.addConstraint(lambda m3: m3 == 'Janelle', ['mother3'])
    
    # Clue 5: The person who is an artist is the person who has brown hair.
    for i in range(1, 6):
        problem.addConstraint(lambda occ, hair, i=i: not (occ == 'artist') or (hair == 'brown'), 
                            [f'occupation{i}', f'hair{i}'])
    
    # Clue 6: The person who is an artist is in the fourth house.
    problem.addConstraint(lambda occ4: occ4 == 'artist', ['occupation4'])
    
    # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    for i in range(1, 6):
        for j in range(1, 6):
            if i >= j:
                continue
            problem.addConstraint(lambda m_i, hair_j, i=i, j=j: not (m_i == 'Penny' and hair_j == 'black') or (i < j), 
                                [f'mother{i}', f'hair{j}'])
    
    # Clue 8: Peter is the person who has black hair.
    for i in range(1, 6):
        problem.addConstraint(lambda name, hair, i=i: not (name == 'Peter') or (hair == 'black'), 
                            [f'name{i}', f'hair{i}'])
    
    # Clue 9: The person who has gray hair is the person who is a teacher.
    for i in range(1, 6):
        problem.addConstraint(lambda hair, occ, i=i: not (hair == 'gray') or (occ == 'teacher'), 
                            [f'hair{i}', f'occupation{i}'])
    
    # Clue 10: Alice is The person whose mother's name is Kailyn.
    for i in range(1, 6):
        problem.addConstraint(lambda name, mother, i=i: not (name == 'Alice') or (mother == 'Kailyn'), 
                            [f'name{i}', f'mother{i}'])
    
    # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
    for i in range(1, 6):
        for j in range(1, 6):
            if i <= j:
                continue
            problem.addConstraint(lambda name_i, bday_j, i=i, j=j: not (name_i == 'Arnold' and bday_j == 'sept') or (i > j), 
                                [f'name{i}', f'birthday{j}'])
    
    # Clue 12: The person who has brown hair is the person whose birthday is in January.
    for i in range(1, 6):
        problem.addConstraint(lambda hair, bday, i=i: not (hair == 'brown') or (bday == 'jan'), 
                            [f'hair{i}', f'birthday{i}'])
    
    # Clue 13: Arnold is the person who has blonde hair.
    for i in range(1, 6):
        problem.addConstraint(lambda name, hair, i=i: not (name == 'Arnold') or (hair == 'blonde'), 
                            [f'name{i}', f'hair{i}'])
    
    # Clue 14: The person whose mother's name is Holly is the person who has black hair.
    for i in range(1, 6):
        problem.addConstraint(lambda mother, hair, i=i: not (mother == 'Holly') or (hair == 'black'), 
                            [f'mother{i}', f'hair{i}'])
    
    # Clue 15: Peter is the person who is a lawyer.
    for i in range(1, 6):
        problem.addConstraint(lambda name, occ, i=i: not (name == 'Peter') or (occ == 'lawyer'), 
                            [f'name{i}', f'occupation{i}'])
    
    # Clue 16: The person whose birthday is in September is somewhere to the left of The person whose mother's name is Kailyn.
    for i in range(1, 6):
        for j in range(1, 6):
            if i >= j:
                continue
            problem.addConstraint(lambda bday_i, mother_j, i=i, j=j: not (bday_i == 'sept' and mother_j == 'Kailyn') or (i < j), 
                                [f'birthday{i}', f'mother{j}'])
    
    # Clue 17: Alice is the person who has gray hair.
    for i in range(1, 6):
        problem.addConstraint(lambda name, hair, i=i: not (name == 'Alice') or (hair == 'gray'), 
                            [f'name{i}', f'hair{i}'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"]
    rows = []
    
    for house in range(1, 6):
        row = [
            str(house),
            solution[f'name{house}'],
            solution[f'birthday{house}'],
            solution[f'mother{house}'],
            solution[f'occupation{house}'],
            solution[f'hair{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))