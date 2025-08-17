import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(5)))

    for name_order in permutations:
        for smoothie_order in permutations:
            for animal_order in permutations:
                for nationality_order in permutations:
                    # Assign based on order
                    name_map = {name: i + 1 for i, name in enumerate(names)}
                    smoothie_map = {smoothie: i + 1 for i, smoothie in enumerate(smoothies)}
                    animal_map = {animal: i + 1 for i, animal in enumerate(animals)}
                    nationality_map = {nationality: i + 1 for i, nationality in enumerate(nationalities)}

                    # Apply constraints
                    if (nationality_map['swede'] + 1 == animal_map['dog'] and
                        abs(animal_map['dog'] - nationality_map['brit']) == 2 and
                        nationality_map['dane'] == animal_map['horse'] and
                        animal_map['bird'] > animal_map['cat'] and
                        animal_map['dog'] + 1 == smoothie_map['lime'] and
                        name_map['Eric'] == animal_map['cat'] and
                        name_map['Bob'] == animal_map['bird'] and
                        smoothie_map['cherry'] + 1 == name_map['Peter'] and
                        animal_map['bird'] == smoothie_map['watermelon'] and
                        smoothie_map['desert'] == animal_map['dog'] and
                        animal_map['horse'] == 3 and
                        nationality_map['norwegian'] == name_map['Alice']):
                        
                        # Construct the solution
                        solution = []
                        for house in houses:
                            name = names[name_order[house - 1]]
                            smoothie = smoothies[smoothie_order[house - 1]]
                            animal = animals[animal_order[house - 1]]
                            nationality = nationalities[nationality_order[house - 1]]
                            solution.append([str(house), name, smoothie, animal, nationality])
                        
                        return json.dumps({
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                                "rows": solution
                            }
                        })

# Run the solver and print the result
print(solve_puzzle())