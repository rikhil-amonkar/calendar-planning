import json
import itertools

def solve_puzzle():
    # Problem setup
    houses = [1, 2, 3]  # left (1) to right (3)
    Names = ["Eric", "Arnold", "Peter"]
    BookGenres = ["mystery", "science fiction", "romance"]
    Vacations = ["mountain", "beach", "city"]

    # Helper to get position (house index starting at 1) of a value in an assignment list by value
    def pos_of(value, assignment):
        # assignment is a list where index 0 corresponds to house 1, etc.
        return assignment.index(value) + 1

    solution = None

    # Iterate over all possible assignments
    for names_assignment in itertools.permutations(Names):
        # Clue 1: Eric is directly left of Arnold -> pos(Eric) + 1 == pos(Arnold)
        if pos_of("Eric", names_assignment) + 1 != pos_of("Arnold", names_assignment):
            continue

        for vac_assignment in itertools.permutations(Vacations):
            # Clue 3: Peter is the person who prefers city breaks.
            if vac_assignment[pos_of("Peter", names_assignment) - 1] != "city":
                continue

            # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
            if pos_of("Peter", names_assignment) <= pos_of("beach", vac_assignment):
                continue

            for book_assignment in itertools.permutations(BookGenres):
                # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
                if pos_of("mystery", book_assignment) >= pos_of("beach", vac_assignment):
                    continue

                # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
                if pos_of("science fiction", book_assignment) != pos_of("beach", vac_assignment):
                    continue

                # All constraints satisfied; build solution
                rows = []
                for h in houses:
                    house_idx = h - 1
                    rows.append([
                        str(h),
                        names_assignment[house_idx],
                        book_assignment[house_idx],
                        vac_assignment[house_idx],
                    ])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Vacation"],
                        "rows": rows
                    }
                }
                # Assuming unique solution; break out of loops
                break
            if solution:
                break
        if solution:
            break

    # If no solution found, still output in required JSON structure with empty rows
    if not solution:
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": []
            }
        }

    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))