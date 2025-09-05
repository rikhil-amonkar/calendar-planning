import itertools
import json

def solve():
    houses = [1, 2, 3]  # indices 0..2 represent houses 1..3

    Names = ['Eric', 'Peter', 'Arnold']
    Smoothies = ['cherry', 'watermelon', 'desert']
    Flowers = ['carnations', 'lilies', 'daffodils']
    Animals = ['cat', 'horse', 'bird']
    Hobbies = ['photography', 'cooking', 'gardening']

    def idx(lst, val):
        return lst.index(val)

    for names in itertools.permutations(Names):
        # Clue 5 implies Peter is not in the leftmost house (must have someone to his left)
        if idx(names, 'Peter') == 0:
            continue

        for smoothies in itertools.permutations(Smoothies):
            for flowers in itertools.permutations(Flowers):
                for animals in itertools.permutations(Animals):
                    # 2. The bird keeper is the person who likes Cherry smoothies.
                    if idx(animals, 'bird') != idx(smoothies, 'cherry'):
                        continue

                    # 7. The Watermelon smoothie lover is the person who keeps horses.
                    if idx(smoothies, 'watermelon') != idx(animals, 'horse'):
                        continue

                    for hobbies in itertools.permutations(Hobbies):
                        # 8. The photography enthusiast is Eric.
                        if idx(hobbies, 'photography') != idx(names, 'Eric'):
                            continue

                        # 3. The person who loves cooking is the Desert smoothie lover.
                        if idx(hobbies, 'cooking') != idx(smoothies, 'desert'):
                            continue

                        # 4. The person who enjoys gardening is the person who loves a carnations arrangement.
                        if idx(hobbies, 'gardening') != idx(flowers, 'carnations'):
                            continue

                        # 6. The person who loves a bouquet of daffodils is the Desert smoothie lover.
                        if idx(flowers, 'daffodils') != idx(smoothies, 'desert'):
                            continue

                        # 1. The person who keeps horses and the photography enthusiast are next to each other.
                        if abs(idx(animals, 'horse') - idx(hobbies, 'photography')) != 1:
                            continue

                        # 5. The person who loves cooking is directly left of Peter.
                        if idx(hobbies, 'cooking') + 1 != idx(names, 'Peter'):
                            continue

                        # If all constraints pass, we've found the solution
                        rows = []
                        for h in range(3):
                            rows.append([
                                str(h + 1),
                                names[h],
                                smoothies[h],
                                flowers[h],
                                animals[h],
                                hobbies[h],
                            ])

                        result = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                "rows": rows
                            }
                        }
                        return result

    # If no solution found (shouldn't happen with valid puzzle)
    return {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
            "rows": []
        }
    }

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, ensure_ascii=False))