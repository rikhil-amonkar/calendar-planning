import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        # Clue 1: Alice is in the second house
        if name_perm[1] != 'Alice':
            continue

        for flower_perm in permutations(flowers):
            for animal_perm in permutations(animals):
                solution = {
                    '1': {'Name': name_perm[0], 'flower': flower_perm[0], 'animal': animal_perm[0]},
                    '2': {'Name': name_perm[1], 'flower': flower_perm[1], 'animal': animal_perm[1]},
                    '3': {'Name': name_perm[2], 'flower': flower_perm[2], 'animal': animal_perm[2]},
                    '4': {'Name': name_perm[3], 'flower': flower_perm[3], 'animal': animal_perm[3]},
                    '5': {'Name': name_perm[4], 'flower': flower_perm[4], 'animal': animal_perm[4]},
                }

                # Check all clues
                # Clue 2: lilies lover is bird keeper
                lilies_house = None
                for house, attrs in solution.items():
                    if attrs['flower'] == 'lilies':
                        lilies_house = house
                        break
                if lilies_house is None or solution[lilies_house]['animal'] != 'bird':
                    continue

                # Clue 3: Peter is right of tulips lover
                tulips_house = None
                peter_house = None
                for house, attrs in solution.items():
                    if attrs['flower'] == 'tulips':
                        tulips_house = house
                    if attrs['Name'] == 'Peter':
                        peter_house = house
                if tulips_house is None or peter_house is None or int(peter_house) <= int(tulips_house):
                    continue

                # Clue 4: fish enthusiast loves daffodils
                fish_house = None
                for house, attrs in solution.items():
                    if attrs['animal'] == 'fish':
                        fish_house = house
                        break
                if fish_house is None or solution[fish_house]['flower'] != 'daffodils':
                    continue

                # Clue 5: Eric keeps horses
                eric_house = None
                for house, attrs in solution.items():
                    if attrs['Name'] == 'Eric':
                        eric_house = house
                        break
                if eric_house is None or solution[eric_house]['animal'] != 'horse':
                    continue

                # Clue 6: two houses between dog owner and Bob
                dog_house = None
                bob_house = None
                for house, attrs in solution.items():
                    if attrs['animal'] == 'dog':
                        dog_house = house
                    if attrs['Name'] == 'Bob':
                        bob_house = house
                if dog_house is None or bob_house is None or abs(int(dog_house) - int(bob_house)) != 3:
                    continue

                # Clue 7: fish enthusiast is directly left of Bob
                if fish_house is None or bob_house is None or int(fish_house) + 1 != int(bob_house):
                    continue

                # Clue 8: Alice is directly left of the person who keeps horses
                alice_house = '2'
                if solution[alice_house]['Name'] != 'Alice':
                    continue
                horse_house = None
                for house, attrs in solution.items():
                    if attrs['animal'] == 'horse':
                        horse_house = house
                        break
                if horse_house is None or int(alice_house) + 1 != int(horse_house):
                    continue

                # Clue 9: carnations directly left of tulips
                carnations_house = None
                for house, attrs in solution.items():
                    if attrs['flower'] == 'carnations':
                        carnations_house = house
                        break
                if carnations_house is None or tulips_house is None or int(carnations_house) + 1 != int(tulips_house):
                    continue

                # Clue 10: cat lover is not in the first house
                if solution['1']['animal'] == 'cat':
                    continue

                # If all clues are satisfied, return the solution
                result = {
                    "solution": {
                        "header": ["House", "Name", "flower", "animal"],
                        "rows": [
                            ["1", solution['1']['Name'], solution['1']['flower'], solution['1']['animal']],
                            ["2", solution['2']['Name'], solution['2']['flower'], solution['2']['animal']],
                            ["3", solution['3']['Name'], solution['3']['flower'], solution['3']['animal']],
                            ["4", solution['4']['Name'], solution['4']['flower'], solution['4']['animal']],
                            ["5", solution['5']['Name'], solution['5']['flower'], solution['5']['animal']]
                        ]
                    }
                }
                return json.dumps(result, indent=2)

    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())