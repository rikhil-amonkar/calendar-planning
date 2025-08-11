import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = ['1', '2', '3']
    names = ['Eric', 'Arnold', 'Peter']
    genres = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']

    # Generate all possible permutations for each attribute
    for name_order in permutations(names):
        # Check clue 1: Eric is directly left of Arnold
        try:
            eric_pos = name_order.index('Eric')
            arnold_pos = name_order.index('Arnold')
            if arnold_pos != eric_pos + 1:
                continue
        except ValueError:
            continue

        for genre_order in permutations(genres):
            for vacation_order in permutations(vacations):
                # Check clue 3: Peter prefers city breaks
                peter_pos = name_order.index('Peter')
                if vacation_order[peter_pos] != 'city':
                    continue

                # Check clue 2: Peter is to the right of the person who loves beach vacations
                beach_pos = vacation_order.index('beach')
                if peter_pos <= beach_pos:
                    continue

                # Check clue 4: mystery is left of beach
                mystery_pos = genre_order.index('mystery')
                if mystery_pos >= beach_pos:
                    continue

                # Check clue 5: science fiction is beach
                if genre_order[beach_pos] != 'science fiction':
                    continue

                # All clues satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "book genres", "type of vacation"],
                        "rows": []
                    }
                }
                for i in range(3):
                    row = [
                        str(i + 1),
                        name_order[i],
                        genre_order[i],
                        vacation_order[i]
                    ]
                    solution["solution"]["rows"].append(row)
                return solution

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))