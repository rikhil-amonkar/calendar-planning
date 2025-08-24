import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5]  # positions left to right

    Names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    Flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    Animals = ['dog', 'horse', 'cat', 'bird', 'fish']

    def pos(item, seq):
        return seq.index(item)

    solution = None

    # Prepare name permutations with fixed positions:
    # Clue 1: Alice is in the second house (index 1)
    # Clue 8 + 5 imply Eric is in the third house (index 2) because horse is in 3 and the horse keeper is Eric
    fixed_names = [None]*5
    fixed_names[1] = 'Alice'
    fixed_names[2] = 'Eric'
    remaining_name_slots = [i for i, v in enumerate(fixed_names) if v is None]  # [0,3,4]
    remaining_names = [n for n in Names if n not in ('Alice', 'Eric')]  # ['Arnold','Bob','Peter']

    for perm_names in itertools.permutations(remaining_names):
        names = fixed_names[:]
        for idx, house_idx in enumerate(remaining_name_slots):
            names[house_idx] = perm_names[idx]

        # Early prune: Bob cannot be at house 1 or 2 due to clue 7 (fish directly left of Bob)
        if pos('Bob', names) in (0, 1, 2):  # 2 also impossible because 2 is Alice
            continue

        # Iterate over flower permutations with constraint 9 (carnations directly left of tulips)
        for flowers in itertools.permutations(Flowers):
            if pos('carnations', flowers) + 1 != pos('tulips', flowers):
                continue

            # Clue 3: Peter is somewhere to the right of the person who loves tulips
            if pos('Peter', names) <= pos('tulips', flowers):
                continue

            # Animals with fixed horse position (house 3, index 2)
            fixed_animals = [None]*5
            fixed_animals[2] = 'horse'  # Clue 5 (horse keeper is Eric) and Clue 8 (Alice left of horse) ensure this
            animal_slots = [i for i, v in enumerate(fixed_animals) if v is None]  # [0,1,3,4]
            remaining_animals = [a for a in Animals if a != 'horse']  # ['dog','cat','bird','fish']

            for perm_animals in itertools.permutations(remaining_animals):
                animals = fixed_animals[:]
                for idx, house_idx in enumerate(animal_slots):
                    animals[house_idx] = perm_animals[idx]

                # Clue 10: The cat lover is not in the first house
                if animals[0] == 'cat':
                    continue

                # Clue 7: The fish enthusiast is directly left of Bob
                if pos('fish', animals) + 1 != pos('Bob', names):
                    continue

                # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils
                if pos('fish', animals) != pos('daffodils', flowers):
                    continue

                # Clue 2: The person who loves the bouquet of lilies is the bird keeper
                if pos('lilies', flowers) != pos('bird', animals):
                    continue

                # Clue 6: There are two houses between the dog owner and Bob
                if abs(pos('dog', animals) - pos('Bob', names)) != 3:
                    continue

                # Clue 8 already structurally enforced: Alice directly left of the person who keeps horses
                if pos('Alice', names) + 1 != pos('horse', animals):
                    continue

                # All constraints satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Flower", "Animal"],
                        "rows": [[str(i+1), names[i], flowers[i], animals[i]] for i in range(5)]
                    }
                }
                return solution

    return None

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False))