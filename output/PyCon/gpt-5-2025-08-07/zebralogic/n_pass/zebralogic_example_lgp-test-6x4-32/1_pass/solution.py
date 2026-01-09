import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)

    # Attributes
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    musics = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    problem = Problem()

    # Add variables: each attribute maps to a house number 1..6
    for n in names:
        problem.addVariable(n, houses)
    for s in styles:
        problem.addVariable(s, houses)
    for m in musics:
        problem.addVariable(m, houses)
    for h in hobbies:
        problem.addVariable(h, houses)

    # All different for each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), styles)
    problem.addConstraint(AllDifferentConstraint(), musics)
    problem.addConstraint(AllDifferentConstraint(), hobbies)

    # Clues as constraints

    # 1. The person who loves rock music is in the fifth house.
    problem.addConstraint(lambda rock: rock == 5, ("rock",))

    # 2. The person who loves classical music and the woodworking hobbyist are next to each other.
    problem.addConstraint(lambda classical, woodworking: abs(classical - woodworking) == 1, ("classical", "woodworking"))

    # 3. The person in a Mediterranean-style villa is the person who loves hip-hop music.
    problem.addConstraint(lambda mediterranean, hiphop: mediterranean == hiphop, ("mediterranean", "hip hop"))

    # 4. There are two houses between Arnold and the person residing in a Victorian house.
    problem.addConstraint(lambda arnold, victorian: abs(arnold - victorian) == 3, ("Arnold", "victorian"))

    # 5. The person who loves jazz music is directly left of Eric.
    problem.addConstraint(lambda jazz, eric: jazz + 1 == eric, ("jazz", "Eric"))

    # 6. The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    problem.addConstraint(lambda hiphop, knitting: hiphop < knitting, ("hip hop", "knitting"))

    # 7. Carol is the person who loves hip-hop music.
    problem.addConstraint(lambda carol, hiphop: carol == hiphop, ("Carol", "hip hop"))

    # 8. The person in a Craftsman-style house is Arnold.
    problem.addConstraint(lambda craftsman, arnold: craftsman == arnold, ("craftsman", "Arnold"))

    # 9. The person in a ranch-style home is Eric.
    problem.addConstraint(lambda ranch, eric: ranch == eric, ("ranch", "Eric"))

    # 10. The woodworking hobbyist is the person residing in a Victorian house.
    problem.addConstraint(lambda woodworking, victorian: woodworking == victorian, ("woodworking", "victorian"))

    # 11. The person who loves country music is in the first house.
    problem.addConstraint(lambda country: country == 1, ("country",))

    # 12. There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    problem.addConstraint(lambda painting, colonial: abs(painting - colonial) == 2, ("painting", "colonial"))

    # 13. Alice is the photography enthusiast.
    problem.addConstraint(lambda alice, photography: alice == photography, ("Alice", "photography"))

    # 14. The person who enjoys gardening is Eric.
    problem.addConstraint(lambda gardening, eric: gardening == eric, ("gardening", "Eric"))

    # 15. Bob is in the third house.
    problem.addConstraint(lambda bob: bob == 3, ("Bob",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    sol = solutions[0]

    # Prepare output rows by house number
    def invert(category_list):
        inv = {}
        for item in category_list:
            inv[sol[item]] = item
        return inv

    inv_names = invert(names)
    inv_styles = invert(styles)
    inv_musics = invert(musics)
    inv_hobbies = invert(hobbies)

    rows = []
    for h in range(1, 7):
        row = [
            str(h),
            inv_names[h],
            inv_styles[h],
            inv_musics[h],
            inv_hobbies[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    solve_puzzle()