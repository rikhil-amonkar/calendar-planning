import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ['Eric', 'Peter', 'Arnold']
    Smoothies = ['cherry', 'watermelon', 'desert']
    Flowers = ['carnations', 'lilies', 'daffodils']
    Animals = ['cat', 'horse', 'bird']
    Hobbies = ['photography', 'cooking', 'gardening']

    solution = None

    for names in itertools.permutations(Names):
        # Peter cannot be in house 1 if cooking must be left of Peter (handled later), but we can prune later.
        for hobbies in itertools.permutations(Hobbies):
            # Clue 8: The photography enthusiast is Eric.
            if hobbies[names.index('Eric')] != 'photography':
                continue

            # Clue 5: The person who loves cooking is directly left of Peter.
            if 'cooking' not in hobbies:
                continue
            idx_cooking = hobbies.index('cooking')
            idx_peter = names.index('Peter')
            if idx_cooking != idx_peter - 1:
                continue

            for smoothies in itertools.permutations(Smoothies):
                # Clue 3: The person who loves cooking is the Desert smoothie lover.
                if smoothies[idx_cooking] != 'desert':
                    continue

                for flowers in itertools.permutations(Flowers):
                    # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                    if flowers[hobbies.index('gardening')] != 'carnations':
                        continue
                    # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                    if flowers[smoothies.index('desert')] != 'daffodils':
                        continue

                    for animals in itertools.permutations(Animals):
                        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
                        if animals[smoothies.index('cherry')] != 'bird':
                            continue
                        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
                        if animals[smoothies.index('watermelon')] != 'horse':
                            continue
                        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
                        if abs(animals.index('horse') - hobbies.index('photography')) != 1:
                            continue

                        # All constraints satisfied
                        solution = {
                            "names": names,
                            "smoothies": smoothies,
                            "flowers": flowers,
                            "animals": animals,
                            "hobbies": hobbies
                        }
                        break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    if not solution:
        raise RuntimeError("No solution found")

    header = ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"]
    rows = []
    for i in houses:
        rows.append([
            str(i + 1),
            solution["names"][i],
            solution["smoothies"][i],
            solution["flowers"][i],
            solution["animals"][i],
            solution["hobbies"][i]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()