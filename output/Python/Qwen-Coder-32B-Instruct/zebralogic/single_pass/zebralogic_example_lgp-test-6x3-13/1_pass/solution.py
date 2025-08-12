import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    books = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(6)))

    # Check each permutation against the clues
    for name_perm in all_permutations:
        for book_perm in all_permutations:
            for occ_perm in all_permutations:
                # Create dictionaries to map positions to values
                name_map = {i + 1: names[name_perm[i]] for i in range(6)}
                book_map = {i + 1: books[book_perm[i]] for i in range(6)}
                occ_map = {i + 1: occupations[occ_perm[i]] for i in range(6)}

                # Check each clue
                if (name_map[book_perm.index(names.index("Alice")) + 1] == "Alice" and
                    book_map[name_perm.index(names.index("Alice")) + 1] == "fantasy" and
                    abs(name_perm.index(names.index("Bob")) - book_perm.index(books.index("mystery"))) == 1 and
                    name_map[book_perm.index(books.index("mystery")) + 1] == "Carol" and
                    occ_map[book_perm.index(books.index("fantasy")) + 1] == "lawyer" and
                    name_map[5] != "Bob" and
                    name_perm.index(names.index("Arnold")) < occ_perm.index(occupations.index("engineer")) and
                    name_map[name_perm.index(names.index("Alice")) + 1] == "Alice" and
                    name_map[name_perm.index(names.index("Alice"))] == name_map[occ_perm.index(occupations.index("nurse")) + 1] and
                    book_map[occ_perm.index(occupations.index("teacher")) + 1] == "biography" and
                    book_perm.index(books.index("historical fiction")) < occ_perm.index(occupations.index("teacher")) and
                    name_map[1] == name_map[occ_perm.index(occupations.index("doctor")) + 1] and
                    book_map[occ_perm.index(occupations.index("artist")) + 1] == "science fiction" and
                    name_map[3] == "Eric" and
                    book_map[5] != "mystery"):
                    
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Book", "Occupation"],
                            "rows": []
                        }
                    }
                    for house in range(1, 7):
                        solution["solution"]["rows"].append([
                            str(house),
                            name_map[house],
                            book_map[house],
                            occ_map[house]
                        ])
                    
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())