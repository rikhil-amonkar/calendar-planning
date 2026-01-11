import itertools
import json

# Step 1: Define the attributes and houses
names = ['Arnold', 'Eric']
book_genres = ['science fiction', 'mystery']
vacations = ['mountain', 'beach']
animals = ['cat', 'horse']
music_genres = ['rock', 'pop']
houses = [1, 2]

# Step 2: Create a possibilities grid
attributes = [names, book_genres, vacations, animals, music_genres]
all_combinations = list(itertools.permutations(names)) + list(itertools.permutations(book_genres)) + \
                   list(itertools.permutations(vacations)) + list(itertools.permutations(animals)) + \
                   list(itertools.permutations(music_genres))

# Generate all possible assignments of attributes to houses
possible_assignments = list(itertools.product(attributes[0], attributes[1], attributes[2], attributes[3], attributes[4]))

# Function to check if an assignment satisfies all clues
def is_valid_assignment(assignment):
    # Unpack the assignment
    (name1, name2), (bg1, bg2), (vac1, vac2), (animal1, animal2), (mg1, mg2) = assignment
    
    # Clue 1: The person who loves beach vacations is Eric.
    if vac1 == 'beach' and name1 != 'Eric':
        return False
    if vac2 == 'beach' and name2 != 'Eric':
        return False
    
    # Clue 2: The person who loves pop music is the person who loves beach vacations.
    if vac1 == 'beach' and mg1 != 'pop':
        return False
    if vac2 == 'beach' and mg2 != 'pop':
        return False
    
    # Clue 3: The person who loves rock music is the person who loves mystery books.
    if mg1 == 'rock' and bg1 != 'mystery':
        return False
    if mg2 == 'rock' and bg2 != 'mystery':
        return False
    
    # Clue 4: The cat lover is not in the second house.
    if animal2 == 'cat':
        return False
    
    # Clue 5: The person who loves mystery books is in the first house.
    if bg2 == 'mystery':
        return False
    
    return True

# Filter assignments based on clues
valid_assignments = [assignment for assignment in itertools.product(
    itertools.permutations(names),
    itertools.permutations(book_genres),
    itertools.permutations(vacations),
    itertools.permutations(animals),
    itertools.permutations(music_genres)
) if is_valid_assignment(assignment)]

# There should be only one valid assignment
assert len(valid_assignments) == 1, "There should be exactly one valid assignment."

# Extract the valid assignment
(name1, name2), (bg1, bg2), (vac1, vac2), (animal1, animal2), (mg1, mg2) = valid_assignments[0]

# Step 4: Output the solution as JSON
solution = {
    "solution": {
        "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
        "rows": [
            ["1", name1, bg1, vac1, animal1, mg1],
            ["2", name2, bg2, vac2, animal2, mg2]
        ]
    }
}

# Convert to JSON
json_solution = json.dumps(solution, indent=4)
print(json_solution)