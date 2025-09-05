import itertools
import json

def solve_puzzle():
    # Houses are indexed 0..5 corresponding to 1..6
    houses = list(range(6))

    # Attributes
    Names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    BookGenres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    Occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

    solutions = []

    for name_perm in itertools.permutations(Names):
        # Clue 12: Eric is in the third house (index 2)
        if name_perm[2] != 'Eric':
            continue

        # Precompute positions of names
        pos_name = {name: name_perm.index(name) for name in Names}

        # Clue 5: Bob is not in the fifth house (index 4)
        if pos_name['Bob'] == 4:
            continue

        # Clue 13 + 3: Mystery not in 5th, and Carol is mystery -> Carol not in 5th
        if pos_name['Carol'] == 4:
            continue

        # Clue 7: Nurse directly left of Alice -> Alice cannot be in house 1 (index 0)
        # Combined with Eric in house 3 (index 2), Alice cannot be in index 2 either.
        # From earlier deduction, Alice can only be in indices 3,4,5 (houses 4,5,6)
        if pos_name['Alice'] not in (3, 4, 5):
            continue

        # Clue 2 + 3: Bob is next to the mystery lover; Carol is the mystery lover -> Bob next to Carol
        if abs(pos_name['Bob'] - pos_name['Carol']) != 1:
            continue

        for book_perm in itertools.permutations(BookGenres):
            # Clue 1: Alice loves fantasy
            if book_perm[pos_name['Alice']] != 'fantasy':
                continue

            # Clue 3: Carol loves mystery
            if book_perm[pos_name['Carol']] != 'mystery':
                continue

            # Clue 13: Mystery not in the fifth house (index 4)
            if book_perm[4] == 'mystery':
                continue

            # Clue 2 (redundant check for safety): Bob next to mystery
            pos_mystery = book_perm.index('mystery')
            if abs(pos_name['Bob'] - pos_mystery) != 1:
                continue

            # Prepare occupations with constraints
            occ = [None] * 6

            # Clue 10: Doctor is in the first house
            occ[0] = 'doctor'

            # Clue 7: Nurse is directly left of Alice
            nurse_pos = pos_name['Alice'] - 1
            if nurse_pos < 0:
                continue
            if occ[nurse_pos] not in (None, 'nurse'):
                continue
            occ[nurse_pos] = 'nurse'

            # Clue 4: Lawyer loves fantasy -> Alice is lawyer
            if occ[pos_name['Alice']] not in (None, 'lawyer'):
                continue
            occ[pos_name['Alice']] = 'lawyer'

            # Clue 11: Science fiction = artist
            pos_scifi = book_perm.index('science fiction')
            if occ[pos_scifi] not in (None, 'artist'):
                continue
            occ[pos_scifi] = 'artist'

            # Clue 8: Biography = teacher
            pos_bio = book_perm.index('biography')
            if occ[pos_bio] not in (None, 'teacher'):
                continue
            occ[pos_bio] = 'teacher'

            # Fill remaining with engineer (should be exactly one remaining)
            remaining_positions = [i for i, v in enumerate(occ) if v is None]
            if len(remaining_positions) != 1:
                continue
            occ[remaining_positions[0]] = 'engineer'

            # Clue 6: Arnold is somewhere to the left of the engineer
            pos_engineer = occ.index('engineer')
            if not (pos_name['Arnold'] < pos_engineer):
                continue

            # Clue 9: Historical fiction is somewhere to the left of the teacher
            pos_hist = book_perm.index('historical fiction')
            pos_teacher = occ.index('teacher')
            if not (pos_hist < pos_teacher):
                continue

            # Validate uniqueness of occupations
            if len(set(occ)) != 6:
                continue

            # All constraints satisfied; record solution
            solution_rows = []
            for i in range(6):
                solution_rows.append([str(i + 1), name_perm[i], book_perm[i], occ[i]])
            solutions.append(solution_rows)

    # Choose the first (should be unique)
    final_solution = solutions[0] if solutions else []

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": final_solution
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))