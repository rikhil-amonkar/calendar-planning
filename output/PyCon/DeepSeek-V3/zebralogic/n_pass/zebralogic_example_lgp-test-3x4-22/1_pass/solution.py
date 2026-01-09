import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1, 2, 3
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"music_{house}", music_genres)
        problem.addVariable(f"child_{house}", children)
        problem.addVariable(f"book_{house}", book_genres)
    
    # All attributes must be different across houses
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"music_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"child_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"book_{house}" for house in houses])
    
    # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books
    for i in range(1, 3):  # Check pairs (1,2) and (2,3)
        problem.addConstraint(
            lambda child1, book2: not (child1 == "Fred" and book2 != "mystery"),
            [f"child_{i}", f"book_{i+1}"]
        )
    # Ensure exactly one Fred child is left of mystery books
    problem.addConstraint(
        lambda c1, c2, c3, b1, b2, b3: (
            (c1 == "Fred" and b2 == "mystery") or
            (c2 == "Fred" and b3 == "mystery")
        ) and not (c1 == "Fred" and b2 != "mystery") and not (c2 == "Fred" and b3 != "mystery"),
        ["child_1", "child_2", "child_3", "book_1", "book_2", "book_3"]
    )
    
    # Clue 2: Peter is in the first house
    problem.addConstraint(lambda name: name == "Peter", ["name_1"])
    
    # Clue 3: The person who loves mystery books is the person who loves classical music
    for house in houses:
        problem.addConstraint(
            lambda book, music, h=house: not (book == "mystery" and music != "classical"),
            [f"book_{house}", f"music_{house}"]
        )
        problem.addConstraint(
            lambda book, music, h=house: not (music == "classical" and book != "mystery"),
            [f"book_{house}", f"music_{house}"]
        )
    
    # Clue 4: The person who loves science fiction books is the person's child is named Meredith
    for house in houses:
        problem.addConstraint(
            lambda book, child, h=house: not (book == "science fiction" and child != "Meredith"),
            [f"book_{house}", f"child_{house}"]
        )
        problem.addConstraint(
            lambda book, child, h=house: not (child == "Meredith" and book != "science fiction"),
            [f"book_{house}", f"child_{house}"]
        )
    
    # Clue 5: Eric is the person who loves mystery books
    for house in houses:
        problem.addConstraint(
            lambda name, book, h=house: not (name == "Eric" and book != "mystery"),
            [f"name_{house}", f"book_{house}"]
        )
        problem.addConstraint(
            lambda name, book, h=house: not (book == "mystery" and name != "Eric"),
            [f"name_{house}", f"book_{house}"]
        )
    
    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books
    problem.addConstraint(
        lambda m1, m2, m3, b1, b2, b3: any(
            (b_i == "romance" and m_j == "rock" and j > i)
            for i in [1, 2, 3] for j in [1, 2, 3]
        ),
        ["music_1", "music_2", "music_3", "book_1", "book_2", "book_3"]
    )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "MusicGenre", "Children", "BookGenre"]
    rows = []
    
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        music = solution[f"music_{house}"]
        child = solution[f"child_{house}"]
        book = solution[f"book_{house}"]
        rows.append([str(house), name, music, child, book])
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))