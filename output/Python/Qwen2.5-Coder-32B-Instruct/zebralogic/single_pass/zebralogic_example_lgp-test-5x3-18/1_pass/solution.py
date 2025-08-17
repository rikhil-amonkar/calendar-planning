import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']

    for name_perm in itertools.permutations(names):
        for flower_perm in itertools.permutations(flowers):
            for animal_perm in itertools.permutations(animals):
                # Assign permutations to houses
                house_dict = {house: {'name': name, 'flower': flower, 'animal': animal}
                              for house, name, flower, animal in zip(houses, name_perm, flower_perm, animal_perm)}

                # Check clues
                if (house_dict[2]['name'] == 'Alice' and
                    house_dict[next(house for house, details in house_dict.items() if details['flower'] == 'lilies')]['animal'] == 'bird' and
                    house_dict.index(next(house for house, details in house_dict.items() if details['name'] == 'Peter')) >
                    house_dict.index(next(house for house, details in house_dict.items() if details['flower'] == 'tulips')) and
                    house_dict[next(house for house, details in house_dict.items() if details['animal'] == 'fish')]['flower'] == 'daffodils' and
                    house_dict[next(house for house, details in house_dict.items() if details['animal'] == 'horse')]['name'] == 'Eric' and
                    abs(house_dict.index(next(house for house, details in house_dict.items() if details['animal'] == 'dog')) -
                        house_dict.index(next(house for house, details in house_dict.items() if details['name'] == 'Bob'))) == 2 and
                    house_dict.index(next(house for house, details in house_dict.items() if details['animal'] == 'fish')) ==
                    house_dict.index(next(house for house, details in house_dict.items() if details['name'] == 'Bob')) - 1 and
                    house_dict.index(next(house for house, details in house_dict.items() if details['name'] == 'Alice')) ==
                    house_dict.index(next(house for house, details in house_dict.items() if details['animal'] == 'horse')) - 1 and
                    house_dict.index(next(house for house, details in house_dict.items() if details['flower'] == 'carnations')) ==
                    house_dict.index(next(house for house, details in house_dict.items() if details['flower'] == 'tulips')) - 1 and
                    house_dict[1]['animal'] != 'cat'):
                    
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Flower", "Animal"],
                            "rows": [[str(house), house_dict[house]['name'], house_dict[house]['flower'], house_dict[house]['animal']] for house in houses]
                        }
                    }
                    return json.dumps(solution)

# Output the solution
print(solve_puzzle())