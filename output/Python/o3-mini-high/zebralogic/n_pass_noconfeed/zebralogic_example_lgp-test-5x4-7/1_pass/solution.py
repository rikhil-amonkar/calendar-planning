import itertools
import json

def solve():
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationals = ["german", "swede", "norwegian", "brit", "dane"]

    # Iterate over permutations with built in constraint prunings.
    for animal_perm in itertools.permutations(animals):
        # Clue 11: The person who keeps horses is in the third house.
        if animal_perm[2] != "horse":
            continue

        for nat_perm in itertools.permutations(nationals):
            # Clue 11/3: The Dane (who keeps horses) must be in the third house.
            if nat_perm[2] != "dane":
                continue

            for name_perm in itertools.permutations(names):
                valid = True
                # Clue 12: The Norwegian is Alice.
                # Clue 6: Eric is the cat lover.
                # Clue 7: Bob is the bird keeper.
                for i in range(5):
                    if nat_perm[i] == "norwegian" and name_perm[i] != "Alice":
                        valid = False
                        break
                    if name_perm[i] == "Alice" and nat_perm[i] != "norwegian":
                        valid = False
                        break
                    if name_perm[i] == "Eric" and animal_perm[i] != "cat":
                        valid = False
                        break
                    if name_perm[i] == "Bob" and animal_perm[i] != "bird":
                        valid = False
                        break
                if not valid:
                    continue

                for smoothie_perm in itertools.permutations(smoothies):
                    # Clue 10: The Desert smoothie lover is the dog owner.
                    try:
                        desert_index = smoothie_perm.index("desert")
                    except ValueError:
                        continue
                    if animal_perm[desert_index] != "dog":
                        continue
                    # Enforce the equivalence (dog owner must have desert smoothie).
                    try:
                        dog_index = animal_perm.index("dog")
                    except ValueError:
                        continue
                    if smoothie_perm[dog_index] != "desert":
                        continue

                    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
                    if dog_index == 4 or smoothie_perm[dog_index + 1] != "lime":
                        continue

                    # Clue 1: The Swedish person is directly left of the dog owner.
                    if dog_index == 0 or nat_perm[dog_index - 1] != "swede":
                        continue

                    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
                    try:
                        cherry_index = smoothie_perm.index("cherry")
                    except ValueError:
                        continue
                    if cherry_index == 4 or name_perm[cherry_index + 1] != "Peter":
                        continue

                    # Clue 9: The bird keeper is the Watermelon smoothie lover.
                    try:
                        bird_index = animal_perm.index("bird")
                    except ValueError:
                        continue
                    if smoothie_perm[bird_index] != "watermelon":
                        continue

                    # Clue 2: There are two houses between the dog owner and the British person.
                    try:
                        brit_index = nat_perm.index("brit")
                    except ValueError:
                        continue
                    if abs(dog_index - brit_index) != 3:
                        continue

                    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
                    # Since Eric is the cat lover and Bob is the bird keeper, we require index(Eric) < index(Bob).
                    try:
                        eric_index = name_perm.index("Eric")
                    except ValueError:
                        continue
                    if bird_index <= eric_index:
                        continue

                    # All constraints satisfied: Build solution list.
                    solution_rows = []
                    # Houses are numbered 1 to 5 in order.
                    for i in range(5):
                        solution_rows.append([
                            str(i + 1),
                            name_perm[i],
                            smoothie_perm[i],
                            animal_perm[i],
                            nat_perm[i]
                        ])
                    
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(result))
                    return

if __name__ == "__main__":
    solve()