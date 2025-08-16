#!/usr/bin/env python3
import json

# Define the sets of attributes.
ALL_NAMES = {'Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric'}
ALL_BOOKS = {'romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction'}
ALL_OCCS = {'artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer'}

# Check the partial assignment (list of houses).
# Each house is a tuple: (name, book, occupation)
def valid_partial(assignment):
    # assignment is a list where index 0 = house 1, index 1 = house 2, ...
    for i, (name, book, occ) in enumerate(assignment):
        # Clue 10: The doctor is in the first house.
        if i == 0 and occ != 'doctor':
            return False
        # Clue 12: Eric is in the third house.
        if i == 2 and name != 'Eric':
            return False
        # Clue 5 and 13: Bob is not in the fifth house and mystery is not in the fifth house.
        if i == 4:
            if name == 'Bob':
                return False
            if book == 'mystery':
                return False
        # Clue 1 and 4: Alice loves fantasy and the lawyer loves fantasy.
        if name == 'Alice':
            if book != 'fantasy' or occ != 'lawyer':
                return False
        # Clue 3: Carol loves mystery.
        if name == 'Carol' and book != 'mystery':
            return False
        # Clue 8 and 11: The teacher must love biography; the artist must love science fiction.
        if occ == 'teacher' and book != 'biography':
            return False
        if occ == 'artist' and book != 'science fiction':
            return False
        # Clue 7: The person who is a nurse is directly left of Alice.
        # If this house is Alice, then the previous house (if exists) must be nurse.
        if name == 'Alice':
            if i == 0:
                return False
            prev_occ = assignment[i-1][2]
            if prev_occ != 'nurse':
                return False
        # Also, if the previous house is nurse then the current house MUST be Alice.
        if i > 0:
            prev_name, prev_book, prev_occ = assignment[i-1]
            if prev_occ == 'nurse' and name != 'Alice':
                return False
        # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
        if occ == 'engineer':
            # Check if any earlier house has name Arnold.
            found = False
            for j in range(i):
                if assignment[j][0] == 'Arnold':
                    found = True
                    break
            if not found:
                return False
        # Clue 9: The person who loves historical fiction is somewhere to the left of the teacher.
        if occ == 'teacher':
            found = False
            for j in range(i):
                if assignment[j][1] == 'historical fiction':
                    found = True
                    break
            if not found:
                return False
    # Clue 2: The person who loves mystery books and Bob are next to each other.
    # Because mystery book is only assigned to Carol (by Clue 3) the requirement becomes: Bob and Carol are adjacent.
    indices = {}
    for idx, (name, book, occ) in enumerate(assignment):
        if name in ('Bob', 'Carol'):
            indices[name] = idx
    if 'Bob' in indices and 'Carol' in indices:
        if abs(indices['Bob'] - indices['Carol']) != 1:
            return False
    return True

# Backtracking recursive search.
def backtrack(assignment, rem_names, rem_books, rem_occs):
    if len(assignment) == 6:
        if valid_partial(assignment):
            return assignment
        else:
            return None

    house_index = len(assignment)
    # For each possible combination from the remaining attributes.
    for name in list(rem_names):
        for book in list(rem_books):
            for occ in list(rem_occs):
                candidate = (name, book, occ)
                
                # Create a new tentative assignment.
                new_assignment = assignment + [candidate]
                
                # Early local checks:
                # House-specific constraints:
                # House 1 (index 0) must be doctor.
                if house_index == 0 and occ != 'doctor':
                    continue
                # House 3 (index 2) must be Eric.
                if house_index == 2 and name != 'Eric':
                    continue
                # House 5 (index 4): Bob and mystery are disallowed.
                if house_index == 4:
                    if name == 'Bob':
                        continue
                    if book == 'mystery':
                        continue
                # If the candidate is Alice, then must have fantasy and lawyer.
                if name == 'Alice':
                    if book != 'fantasy' or occ != 'lawyer':
                        continue
                    if house_index == 0:
                        continue  # cannot be in the first house because nurse must be left of Alice.
                    # Additionally, check that the previous house is already assigned and is nurse.
                    if assignment and assignment[-1][2] != 'nurse':
                        continue
                # If the candidate is Carol, then must have mystery.
                if name == 'Carol' and book != 'mystery':
                    continue
                # If occ is teacher, then book must be biography.
                if occ == 'teacher' and book != 'biography':
                    continue
                # If occ is artist, then book must be science fiction.
                if occ == 'artist' and book != 'science fiction':
                    continue
                # Clue 7: If previous house is nurse then current must be Alice.
                if house_index > 0:
                    if assignment[-1][2] == 'nurse' and name != 'Alice':
                        continue
                # Clue 6: If occ is engineer, ensure that an Arnold has already been assigned.
                if occ == 'engineer':
                    if not any(a_name == 'Arnold' for (a_name, a_book, a_occ) in assignment):
                        continue
                # Clue 9: If occ is teacher, ensure that a house before has historical fiction.
                if occ == 'teacher':
                    if not any(a_book == 'historical fiction' for (a_name, a_book, a_occ) in assignment):
                        continue

                # Build new remaining sets.
                new_rem_names = rem_names - {name}
                new_rem_books = rem_books - {book}
                new_rem_occs = rem_occs - {occ}
                
                # Check global constraints on the new assignment.
                if not valid_partial(new_assignment):
                    continue

                result = backtrack(new_assignment, new_rem_names, new_rem_books, new_rem_occs)
                if result is not None:
                    return result
    return None

def solve_puzzle():
    solution = backtrack([], ALL_NAMES, ALL_BOOKS, ALL_OCCS)
    return solution

def main():
    sol = solve_puzzle()
    if sol is None:
        output = {"solution": {"header": ["House", "Name", "BookGenre", "Occupation"], "rows": []}}
    else:
        # Build rows: houses numbered 1 through 6 in order.
        rows = []
        for i, (name, book, occ) in enumerate(sol):
            row = [str(i+1), name, book, occ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "BookGenre", "Occupation"], "rows": rows}}
    print(json.dumps(output, indent=2))
    
if __name__ == '__main__':
    main()