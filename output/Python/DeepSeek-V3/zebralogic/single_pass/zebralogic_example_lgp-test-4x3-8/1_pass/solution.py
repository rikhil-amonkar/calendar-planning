import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    houses = ['1', '2', '3', '4']

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for music_perm in permutations(music_genres):
                # Assign each permutation to houses 1-4
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': str(i + 1),
                        'Name': name_perm[i],
                        'Hair Color': hair_perm[i],
                        'Music Genre': music_perm[i]
                    })

                # Check all constraints
                valid = True

                # Constraint 1: Eric has red hair
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house
                        break
                if not eric_house or eric_house['Hair Color'] != 'red':
                    valid = False
                    continue

                # Constraint 2: classical is directly left of blonde
                classical_pos = None
                blonde_pos = None
                for i in range(4):
                    if assignment[i]['Music Genre'] == 'classical':
                        classical_pos = i
                    if assignment[i]['Hair Color'] == 'blonde':
                        blonde_pos = i
                if classical_pos is None or blonde_pos is None or classical_pos + 1 != blonde_pos:
                    valid = False
                    continue

                # Constraint 3: brown hair is not in house 1
                if assignment[0]['Hair Color'] == 'brown':
                    valid = False
                    continue

                # Constraint 4: pop is not in house 3
                if assignment[2]['Music Genre'] == 'pop':
                    valid = False
                    continue

                # Constraint 5: classical is in house 1
                if assignment[0]['Music Genre'] != 'classical':
                    valid = False
                    continue

                # Constraint 6: jazz is the person with red hair
                jazz_house = None
                for house in assignment:
                    if house['Music Genre'] == 'jazz':
                        jazz_house = house
                        break
                if not jazz_house or jazz_house['Hair Color'] != 'red':
                    valid = False
                    continue

                # Constraint 7: rock is Arnold
                rock_house = None
                for house in assignment:
                    if house['Music Genre'] == 'rock':
                        rock_house = house
                        break
                if not rock_house or rock_house['Name'] != 'Arnold':
                    valid = False
                    continue

                # Constraint 8: Peter is right of rock
                rock_pos = None
                peter_pos = None
                for i in range(4):
                    if assignment[i]['Name'] == 'Peter':
                        peter_pos = i
                    if assignment[i]['Music Genre'] == 'rock':
                        rock_pos = i
                if rock_pos is None or peter_pos is None or peter_pos <= rock_pos:
                    valid = False
                    continue

                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Hair Color", "Music Genre"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Hair Color'],
                            house['Music Genre']
                        ])
                    return solution

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))