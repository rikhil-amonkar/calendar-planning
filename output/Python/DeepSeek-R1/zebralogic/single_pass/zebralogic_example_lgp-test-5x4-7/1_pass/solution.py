import itertools
import json

def satisfies_all_constraints(assignment):
    # Extract the lists
    names = assignment['name']
    smoothies = assignment['smoothie']
    animals = assignment['animal']
    nationalities = assignment['nationality']
    
    try:
        dog_index = animals.index('dog')
    except ValueError:
        return False
    try:
        bird_index = animals.index('bird')
    except ValueError:
        return False
    try:
        cat_index = animals.index('cat')
    except ValueError:
        return False
    try:
        brit_index = nationalities.index('brit')
    except ValueError:
        return False
    try:
        swede_index = nationalities.index('swede')
    except ValueError:
        return False
    try:
        norwegian_index = nationalities.index('norwegian')
    except ValueError:
        return False

    # Constraint 1: Swedish directly left of dog owner.
    if swede_index != dog_index - 1:
        return False

    # Constraint 2: Two houses between dog owner and British.
    if abs(dog_index - brit_index) != 3:
        return False

    # Constraint 4: Bird keeper right of cat lover.
    if bird_index <= cat_index:
        return False

    # Constraint 5: Dog owner directly left of Lime smoothie.
    if dog_index == 4:
        return False
    if smoothies[dog_index+1] != 'lime':
        return False

    # Constraint 6: Eric is the cat lover.
    if names[cat_index] != 'Eric':
        return False

    # Constraint 7: Bob is the bird keeper.
    if names[bird_index] != 'Bob':
        return False

    # Constraint 8: Cherry smoothie directly left of Peter.
    found_cherry = False
    for i in range(4):
        if smoothies[i] == 'cherry' and names[i+1] == 'Peter':
            found_cherry = True
            break
    if not found_cherry:
        return False

    # Constraint 9: Bird keeper is Watermelon smoothie lover.
    if smoothies[bird_index] != 'watermelon':
        return False

    # Constraint 10: Desert smoothie lover is dog owner.
    if smoothies[dog_index] != 'desert':
        return False

    # Constraint 12: Norwegian is Alice.
    if names[norwegian_index] != 'Alice':
        return False

    return True

def main():
    names_list = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies_list = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals_base = ['dog', 'bird', 'fish', 'cat']  # without 'horse'
    nationalities_base = ['german', 'swede', 'norwegian', 'brit']  # without 'dane'
    
    solution_found = None
    
    for names in itertools.permutations(names_list):
        for smoothies in itertools.permutations(smoothies_list):
            for animals0 in itertools.permutations(animals_base):
                animals = [
                    animals0[0],
                    animals0[1],
                    'horse',
                    animals0[2],
                    animals0[3]
                ]
                for nationalities0 in itertools.permutations(nationalities_base):
                    nationalities = [
                        nationalities0[0],
                        nationalities0[1],
                        'dane',
                        nationalities0[2],
                        nationalities0[3]
                    ]
                    assignment = {
                        'name': names,
                        'smoothie': smoothies,
                        'animal': animals,
                        'nationality': nationalities
                    }
                    if satisfies_all_constraints(assignment):
                        solution_found = assignment
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    if not solution_found:
        print(json.dumps({"solution": {"header": [], "rows": []}}))
        return
    
    # Format the solution
    header = ["House", "Name", "Smoothie", "Animal", "Nationality"]
    rows = []
    for i in range(5):
        row = [
            str(i+1),
            solution_found['name'][i],
            solution_found['smoothie'][i],
            solution_found['animal'][i],
            solution_found['nationality'][i]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()