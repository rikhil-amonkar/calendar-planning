import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1-4)
    houses = [1, 2, 3, 4]
    
    # Define domains for each attribute
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'hair_{house}', hair_colors)
        problem.addVariable(f'music_{house}', music_genres)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'hair_{h}' for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'music_{h}' for h in houses])
    
    # Clue 1: Eric is the person who has red hair.
    for house in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Eric') or (hair == 'red'),
            [f'name_{house}', f'hair_{house}']
        )
    
    # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
    for i in range(1, 4):
        problem.addConstraint(
            lambda music_left, hair_right: not (music_left == 'classical') or (hair_right == 'blonde'),
            [f'music_{i}', f'hair_{i+1}']
        )
    
    # Clue 3: The person who has brown hair is not in the first house.
    problem.addConstraint(lambda hair: hair != 'brown', ['hair_1'])
    
    # Clue 4: The person who loves pop music is not in the third house.
    problem.addConstraint(lambda music: music != 'pop', ['music_3'])
    
    # Clue 5: The person who loves classical music is in the first house.
    problem.addConstraint(lambda music: music == 'classical', ['music_1'])
    
    # Clue 6: The person who loves jazz music is the person who has red hair.
    for house in houses:
        problem.addConstraint(
            lambda music, hair: not (music == 'jazz') or (hair == 'red'),
            [f'music_{house}', f'hair_{house}']
        )
    
    # Clue 7: The person who loves rock music is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda music, name: not (music == 'rock') or (name == 'Arnold'),
            [f'music_{house}', f'name_{house}']
        )
    
    # Clue 8: Peter is somewhere to the right of the person who loves rock music.
    def peter_right_of_rock(music1, name1, music2, name2, music3, name3, music4, name4):
        rock_house = None
        peter_house = None
        
        if music1 == 'rock':
            rock_house = 1
        elif music2 == 'rock':
            rock_house = 2
        elif music3 == 'rock':
            rock_house = 3
        elif music4 == 'rock':
            rock_house = 4
            
        if name1 == 'Peter':
            peter_house = 1
        elif name2 == 'Peter':
            peter_house = 2
        elif name3 == 'Peter':
            peter_house = 3
        elif name4 == 'Peter':
            peter_house = 4
            
        return peter_house > rock_house
    
    problem.addConstraint(
        peter_right_of_rock,
        ['music_1', 'name_1', 'music_2', 'name_2', 'music_3', 'name_3', 'music_4', 'name_4']
    )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HairColor", "MusicGenre"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        hair = solution[f'hair_{house}']
        music = solution[f'music_{house}']
        rows.append([str(house), name, hair, music])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))