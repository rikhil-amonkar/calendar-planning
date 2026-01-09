import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    genres = ["science fiction", "romance", "mystery"]

    p = Problem()

    # Add variables: each attribute value maps to a house position
    for n in names:
        p.addVariable(f"name_{n}", houses)
    for s in smoothies:
        p.addVariable(f"smoothie_{s}", houses)
    for g in genres:
        p.addVariable(f"genre_{g}", houses)

    # Uniqueness constraints within each category
    p.addConstraint(AllDifferentConstraint(), [f"name_{n}" for n in names])
    p.addConstraint(AllDifferentConstraint(), [f"smoothie_{s}" for s in smoothies])
    p.addConstraint(AllDifferentConstraint(), [f"genre_{g}" for g in genres])

    # Clue 1: Cherry smoothie is somewhere to the left of the person who loves mystery books.
    p.addConstraint(lambda cherry, mystery: cherry < mystery, ["smoothie_cherry", "genre_mystery"])

    # Clue 2: Arnold is the person who loves mystery books.
    p.addConstraint(lambda arnold, mystery: arnold == mystery, ["name_Arnold", "genre_mystery"])

    # Clue 3: Science fiction is not in the first house.
    p.addConstraint(lambda sci: sci != 1, ["genre_science fiction"])

    # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
    p.addConstraint(lambda desert, mystery: desert + 1 == mystery, ["smoothie_desert", "genre_mystery"])

    # Clue 5: Peter is in the first house.
    p.addConstraint(lambda peter: peter == 1, ["name_Peter"])

    solution = p.getSolution()
    if solution is None:
        raise RuntimeError("No solution found")

    # Invert mapping to get assignments per house
    house_rows = []
    for h in houses:
        name_val = next(n for n in names if solution[f"name_{n}"] == h)
        smoothie_val = next(s for s in smoothies if solution[f"smoothie_{s}"] == h)
        genre_val = next(g for g in genres if solution[f"genre_{g}"] == h)
        house_rows.append([str(h), name_val, smoothie_val, genre_val])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": house_rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()