import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4]  # left to right

    Names = ['Arnold', 'Peter', 'Eric', 'Alice']
    HouseStyles = ['craftsman', 'colonial', 'victorian', 'ranch']
    HairColors = ['red', 'blonde', 'black', 'brown']
    Children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    BookGenres = ['mystery', 'fantasy', 'romance', 'science fiction']

    solutions = []

    # Iterate over assignments with pruning based on clues
    for names in permutations(Names):
        # names[i] is the person in house i+1

        # Clue 12 + 9: Eric has black hair, and black hair is in house 2 -> Eric is in house 2
        if names[1] != 'Eric':
            continue

        # Clue 4 + 6: House 4 child Samantha; Peter's child is Bella -> Peter cannot be in house 4
        if names[3] == 'Peter':
            continue

        # Clue 7 + 3: Arnold has red hair; house 4 has brown hair -> Arnold not in house 4
        if names[3] == 'Arnold':
            continue

        for styles in permutations(HouseStyles):
            # Clue 1: Craftsman is in the third house
            if styles[2] != 'craftsman':
                continue

            # Clue 8: Alice lives in a colonial-style house
            alice_house = names.index('Alice')
            if styles[alice_house] != 'colonial':
                continue

            for hairs in permutations(HairColors):
                # Clue 9: Black hair is in the second house
                if hairs[1] != 'black':
                    continue
                # Clue 3: Brown hair is in the fourth house
                if hairs[3] != 'brown':
                    continue
                # Clue 12: Eric has black hair (Eric is in house 2 already)
                if hairs[names.index('Eric')] != 'black':
                    continue
                # Clue 7: Arnold has red hair
                if hairs[names.index('Arnold')] != 'red':
                    continue

                for kids in permutations(Children):
                    # Clue 4: Samantha is in the fourth house
                    if kids[3] != 'Samantha':
                        continue
                    # Clue 6: Peter's child is Bella
                    if kids[names.index('Peter')] != 'Bella':
                        continue
                    # Clue 11: Arnold's child is Meredith
                    if kids[names.index('Arnold')] != 'Meredith':
                        continue

                    for books in permutations(BookGenres):
                        # Clue 2: Alice loves romance books
                        if books[names.index('Alice')] != 'romance':
                            continue
                        # Clue 10: Peter loves fantasy books
                        if books[names.index('Peter')] != 'fantasy':
                            continue
                        # Clue 13: Arnold loves science fiction books
                        if books[names.index('Arnold')] != 'science fiction':
                            continue

                        # Clue 5: Ranch is to the right of red hair (Arnold's hair)
                        red_house = hairs.index('red')  # index 0..3
                        ranch_house = styles.index('ranch')
                        if not (ranch_house > red_house):
                            continue

                        # All constraints satisfied
                        solutions.append((names, styles, hairs, kids, books))

    # Expect exactly one solution; pick the first if multiple (shouldn't happen)
    if not solutions:
        raise RuntimeError("No solution found.")
    names, styles, hairs, kids, books = solutions[0]

    # Build JSON output
    header = ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"]
    rows = []
    for i in range(4):
        rows.append([
            str(i+1),
            names[i],
            styles[i],
            hairs[i],
            kids[i],
            books[i]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return json.dumps(output, ensure_ascii=False)

if __name__ == "__main__":
    print(solve_puzzle())