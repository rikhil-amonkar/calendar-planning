import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3]

    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]

    problem = Problem()

    # Create variables: each attribute value maps to a house number
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for m in music_genres:
        problem.addVariable(f"Music_{m}", houses)
    for c in children:
        problem.addVariable(f"Child_{c}", houses)
    for b in book_genres:
        problem.addVariable(f"Book_{b}", houses)

    # All different within each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Music_{m}" for m in music_genres])
    problem.addConstraint(AllDifferentConstraint(), [f"Child_{c}" for c in children])
    problem.addConstraint(AllDifferentConstraint(), [f"Book_{b}" for b in book_genres])

    # Clue 2: Peter is in the first house.
    problem.addConstraint(lambda x: x == 1, ("Name_Peter",))

    # Clue 5: Eric is the person who loves mystery books.
    problem.addConstraint(lambda a, b: a == b, ("Name_Eric", "Book_mystery"))

    # Clue 3: The person who loves mystery books is the person who loves classical music.
    problem.addConstraint(lambda a, b: a == b, ("Book_mystery", "Music_classical"))

    # Clue 1: The person whose child is named Fred is directly left of the person who loves mystery books.
    problem.addConstraint(lambda fred, myst: fred + 1 == myst, ("Child_Fred", "Book_mystery"))

    # Clue 4: The person who loves science fiction books is the one whose child is Meredith.
    problem.addConstraint(lambda sci, mer: sci == mer, ("Book_science fiction", "Child_Meredith"))

    # Clue 6: Rock music is to the right of the romance books.
    problem.addConstraint(lambda rock, romance: rock > romance, ("Music_rock", "Book_romance"))

    solutions = problem.getSolutions()
    if not solutions:
        result = {
            "solution": {
                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    # Choose the first (solutions should be unique given the constraints)
    sol = solutions[0]

    def value_at_house(prefix, values, house):
        for v in values:
            if sol[f"{prefix}_{v}"] == house:
                return v
        return None

    rows = []
    for h in houses:
        name = value_at_house("Name", names, h)
        music = value_at_house("Music", music_genres, h)
        child = value_at_house("Child", children, h)
        book = value_at_house("Book", book_genres, h)
        rows.append([str(h), name, music, child, book])

    output = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()