import itertools
import json

def solve_puzzle():
    # Define the attributes
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(flowers)) + \
                       list(itertools.permutations(animals)) + \
                       list(itertools.permutations(hobbies))

    # Function to check if a given permutation set satisfies all constraints
    def is_valid_solution(name_perm, smoothie_perm, flower_perm, animal_perm, hobby_perm):
        # Create a dictionary for easy lookup
        house_data = {
            1: {'name': name_perm[0], 'smoothie': smoothie_perm[0], 'flower': flower_perm[0], 'animal': animal_perm[0], 'hobby': hobby_perm[0]},
            2: {'name': name_perm[1], 'smoothie': smoothie_perm[1], 'flower': flower_perm[1], 'animal': animal_perm[1], 'hobby': hobby_perm[1]},
            3: {'name': name_perm[2], 'smoothie': smoothie_perm[2], 'flower': flower_perm[2], 'animal': animal_perm[2], 'hobby': hobby_perm[2]}
        }

        # Check each clue
        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
        horse_house = [house for house, data in house_data.items() if data['animal'] == 'horse'][0]
        photo_house = [house for house, data in house_data.items() if data['hobby'] == 'photography'][0]
        if abs(horse_house - photo_house) != 1:
            return False

        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
        if house_data[next(house for house, data in house_data.items() if data['animal'] == 'bird')]['smoothie'] != 'cherry':
            return False

        # Clue 3: The person who loves cooking is the Desert smoothie lover.
        if house_data[next(house for house, data in house_data.items() if data['hobby'] == 'cooking')]['smoothie'] != 'desert':
            return False

        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
        if house_data[next(house for house, data in house_data.items() if data['hobby'] == 'gardening')]['flower'] != 'carnations':
            return False

        # Clue 5: The person who loves cooking is directly left of Peter.
        cooking_house = next(house for house, data in house_data.items() if data['hobby'] == 'cooking')
        peter_house = next(house for house, data in house_data.items() if data['name'] == 'Peter')
        if cooking_house + 1 != peter_house:
            return False

        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
        if house_data[next(house for house, data in house_data.items() if data['flower'] == 'daffodils')]['smoothie'] != 'desert':
            return False

        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
        if house_data[horse_house]['smoothie'] != 'watermelon':
            return False

        # Clue 8: The photography enthusiast is Eric.
        if house_data[photo_house]['name'] != 'Eric':
            return False

        return True

    # Try all combinations
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for flower_perm in itertools.permutations(flowers):
                for animal_perm in itertools.permutations(animals):
                    for hobby_perm in itertools.permutations(hobbies):
                        if is_valid_solution(name_perm, smoothie_perm, flower_perm, animal_perm, hobby_perm):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                    "rows": [
                                        ["1", name_perm[0], smoothie_perm[0], flower_perm[0], animal_perm[0], hobby_perm[0]],
                                        ["2", name_perm[1], smoothie_perm[1], flower_perm[1], animal_perm[1], hobby_perm[1]],
                                        ["3", name_perm[2], smoothie_perm[2], flower_perm[2], animal_perm[2], hobby_perm[2]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())