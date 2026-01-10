import itertools
import json

def main():
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    books = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Generate all possible name assignments that satisfy the constraints
    for name_perm in itertools.permutations(names):
        assignment = list(name_perm)
        # Check fixed constraints on names
        if assignment[2] != 'Eric':  # House 3 is Eric
            continue
        if assignment[4] == 'Bob':   # Bob not in house 5
            continue
        if assignment[4] == 'Carol': # Carol not in house 5
            continue
        if assignment[0] == 'Alice': # Alice not in house 1
            continue
        
        # Find Carol and Bob positions
        carol_index = assignment.index('Carol')
        bob_index = assignment.index('Bob')
        # Carol and Bob must be adjacent
        if abs(carol_index - bob_index) != 1:
            continue
            
        # Now generate book assignments
        for book_perm in itertools.permutations(books):
            book_assignment = list(book_perm)
            # Alice must have fantasy book
            alice_index = assignment.index('Alice')
            if book_assignment[alice_index] != 'fantasy':
                continue
            # Carol must have mystery book
            if book_assignment[carol_index] != 'mystery':
                continue
            # Mystery book not in house 5
            if book_assignment[4] == 'mystery':
                continue
            # All books unique already by permutation
                
            # Now generate occupation assignments
            for occ_perm in itertools.permutations(occupations):
                occ_assignment = list(occ_perm)
                # House 1 is doctor
                if occ_assignment[0] != 'doctor':
                    continue
                # Alice is lawyer
                if occ_assignment[alice_index] != 'lawyer':
                    continue
                # Nurse is directly left of Alice
                if alice_index == 0:
                    continue  # Alice can't be in house 1
                if occ_assignment[alice_index-1] != 'nurse':
                    continue
                # Biography book and teacher occupation same house
                try:
                    bio_index = book_assignment.index('biography')
                except ValueError:
                    continue
                if occ_assignment[bio_index] != 'teacher':
                    continue
                # Science fiction book and artist occupation same house
                try:
                    sf_index = book_assignment.index('science fiction')
                except ValueError:
                    continue
                if occ_assignment[sf_index] != 'artist':
                    continue
                # Historical fiction left of teacher (biography)
                try:
                    hf_index = book_assignment.index('historical fiction')
                except ValueError:
                    continue
                if hf_index >= bio_index:
                    continue
                # Arnold left of engineer
                try:
                    arnold_index = assignment.index('Arnold')
                    engineer_index = occ_assignment.index('engineer')
                except ValueError:
                    continue
                if arnold_index >= engineer_index:
                    continue
                # All occupations unique already by permutation
                
                # Found solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Occupation"],
                        "rows": []
                    }
                }
                for i in range(6):
                    solution["solution"]["rows"].append([
                        str(i+1),
                        assignment[i],
                        book_assignment[i],
                        occ_assignment[i]
                    ])
                print(json.dumps(solution, indent=2))
                return
                
    print("No solution found")

if __name__ == '__main__':
    main()