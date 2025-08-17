import itertools
import json

def main():
    nationalities_list = ['german', 'swede', 'norwegian', 'brit', 'dane']
    animals_list = ['horse', 'dog', 'bird', 'fish', 'cat']
    names_list = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies_list = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']

    solution_found = False

    for nationalities in itertools.permutations(nationalities_list):
        if nationalities[2] != 'dane':
            continue  # Clue 3 and 11
        for animals in itertools.permutations(animals_list):
            if animals[2] != 'horse':
                continue  # Clue 11
            for names in itertools.permutations(names_list):
                for smoothies in itertools.permutations(smoothies_list):
                    if check_constraints(nationalities, animals, names, smoothies):
                        solution = build_solution(nationalities, animals, names, smoothies)
                        print(json.dumps(solution))
                        solution_found = True
                        return

    if not solution_found:
        print(json.dumps({"solution": {}}))

def check_constraints(nationalities, animals, names, smoothies):
    # Clue 1: The Swedish person is directly left of the dog owner.
    swede_index = None
    for i in range(5):
        if nationalities[i] == 'swede':
            swede_index = i
            break
    if swede_index is None or swede_index + 1 >= 5 or animals[swede_index + 1] != 'dog':
        return False

    # Clue 2: Two houses between dog owner and British person.
    dog_house = None
    brit_house = None
    for i in range(5):
        if animals[i] == 'dog':
            dog_house = i
        if nationalities[i] == 'brit':
            brit_house = i
    if dog_house is None or brit_house is None or abs(dog_house - brit_house) != 3:
        return False

    # Clue 4: Bird keeper is to the right of cat lover.
    bird_house = None
    cat_house = None
    for i in range(5):
        if animals[i] == 'bird':
            bird_house = i
        if animals[i] == 'cat':
            cat_house = i
    if bird_house is None or cat_house is None or bird_house <= cat_house:
        return False

    # Clue 5: Dog owner directly left of lime smoothie.
    if dog_house + 1 >= 5 or smoothies[dog_house + 1] != 'lime':
        return False

    # Clue 6: Eric is cat lover.
    eric_index = None
    for i in range(5):
        if names[i] == 'Eric' and animals[i] == 'cat':
            eric_index = i
            break
    if eric_index is None:
        return False

    # Clue 7: Bob is bird keeper.
    bob_index = None
    for i in range(5):
        if names[i] == 'Bob' and animals[i] == 'bird':
            bob_index = i
            break
    if bob_index is None:
        return False

    # Clue 8: Cherry smoothie directly left of Peter.
    cherry_peter = False
    for i in range(4):  # i can be 0-3
        if smoothies[i] == 'cherry' and names[i+1] == 'Peter':
            cherry_peter = True
            break
    if not cherry_peter:
        return False

    # Clue 9: Bird keeper is watermelon smoothie lover.
    if smoothies[bob_index] != 'watermelon':
        return False

    # Clue 10: Desert smoothie lover is dog owner.
    if smoothies[dog_house] != 'desert':
        return False

    # Clue 12: Norwegian is Alice.
    norwegian_index = None
    for i in range(5):
        if nationalities[i] == 'norwegian':
            norwegian_index = i
            break
    if norwegian_index is None or names[norwegian_index] != 'Alice':
        return False

    return True

def build_solution(nationalities, animals, names, smoothies):
    header = ["House", "Name", "Smoothie", "Animal", "Nationality"]
    rows = []
    for i in range(5):
        house_num = str(i + 1)
        name = names[i]
        smoothie = smoothies[i]
        animal = animals[i]
        nationality = nationalities[i]
        rows.append([house_num, name, smoothie, animal, nationality])
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    main()