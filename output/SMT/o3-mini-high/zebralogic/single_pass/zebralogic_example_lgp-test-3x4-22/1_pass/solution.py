from z3 import *
import json

def solve():
    s = Solver()

    # Define Z3 integer variables for each category.
    # Each variable represents the house number (1, 2, or 3) for that attribute.
    names = {
        "Peter": Int("Peter"),
        "Eric": Int("Eric"),
        "Arnold": Int("Arnold")
    }
    musics = {
        "pop": Int("pop"),
        "rock": Int("rock"),
        "classical": Int("classical")
    }
    children = {
        "Fred": Int("Fred"),
        "Meredith": Int("Meredith"),
        "Bella": Int("Bella")
    }
    # Note: Because variable names cannot have spaces we name the variable for "science fiction" as "science_fiction"
    books = {
        "mystery": Int("mystery"),
        "romance": Int("romance"),
        "science fiction": Int("science_fiction")
    }

    # All variables must have a value from 1 to 3.
    all_vars = list(names.values()) + list(musics.values()) + list(children.values()) + list(books.values())
    for v in all_vars:
        s.add(v >= 1, v <= 3)

    # Each category is a permutation of houses.
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(musics.values())))
    s.add(Distinct(list(children.values())))
    s.add(Distinct(list(books.values())))

    # Clue 2: Peter is in the first house.
    s.add(names["Peter"] == 1)

    # Clue 1: The person whose child is Fred is directly left of the person who loves mystery books.
    # This means: Child(Fred) + 1 == Book(mystery)
    s.add(children["Fred"] + 1 == books["mystery"])

    # Clue 3: The person who loves mystery books is the person who loves classical music.
    s.add(books["mystery"] == musics["classical"])

    # Clue 4: The person who loves science fiction books is the person whose child is Meredith.
    s.add(books["science fiction"] == children["Meredith"])

    # Clue 5: Eric is the person who loves mystery books.
    s.add(names["Eric"] == books["mystery"])

    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
    s.add(musics["rock"] > books["romance"])

    if s.check() == sat:
        m = s.model()
        # Prepare the solution structure.
        solution = {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": []
        }

        # For houses 1 through 3, find the corresponding attributes.
        for house in range(1, 4):
            # Find the name assigned to this house.
            name_val = [name for name, var in names.items() if m[var].as_long() == house][0]
            # Find the music genre assigned to this house.
            music_val = [music for music, var in musics.items() if m[var].as_long() == house][0]
            # Find the child's name in this house.
            child_val = [child for child, var in children.items() if m[var].as_long() == house][0]
            # Find the book genre assigned to this house.
            book_val = [book for book, var in books.items() if m[var].as_long() == house][0]

            solution["rows"].append([str(house), name_val, music_val, child_val, book_val])

        # Output the solution in the required JSON format.
        output = {"solution": solution}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    solve()