import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3]  # left to right

    Names = ['Arnold', 'Eric', 'Peter']
    Music = ['pop', 'rock', 'classical']
    Children = ['Fred', 'Meredith', 'Bella']
    Books = ['mystery', 'romance', 'science fiction']

    solutions = []

    for N in permutations(Names):
        # Clue 2: Peter is in the first house.
        if N[0] != 'Peter':
            continue

        for B in permutations(Books):
            # Clue 5: Eric is the person who loves mystery books.
            if N.index('Eric') != B.index('mystery'):
                continue

            for M in permutations(Music):
                # Clue 3: The person who loves mystery books is the person who loves classical music.
                if B.index('mystery') != M.index('classical'):
                    continue

                # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
                if not (M.index('rock') > B.index('romance')):
                    continue

                for C in permutations(Children):
                    # Clue 1: Child Fred is directly left of the person who loves mystery books.
                    if C.index('Fred') + 1 != B.index('mystery'):
                        continue

                    # Clue 4: Sci-fi books person has child Meredith.
                    if B.index('science fiction') != C.index('Meredith'):
                        continue

                    # If all constraints satisfied, record solution
                    solution = {
                        "N": N,
                        "M": M,
                        "C": C,
                        "B": B
                    }
                    solutions.append(solution)

    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")
    # If multiple solutions, choose the first (puzzle is expected to have a unique solution)
    sol = solutions[0]

    rows = []
    for i, h in enumerate(houses):
        rows.append([
            str(h),
            sol["N"][i],
            sol["M"][i],
            sol["C"][i],
            sol["B"][i]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))