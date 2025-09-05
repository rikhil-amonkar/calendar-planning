import z3
import json

def main():
    solver = z3.Solver()
    n_houses = 6

    # Define enums
    NameSort, (Eric, Alice, Arnold, Carol, Peter, Bob) = z3.EnumSort('Name', ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob'])
    HouseStyleSort, (mediterranean, modern, craftsman, ranch, colonial, victorian) = z3.EnumSort('HouseStyle', ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian'])
    MusicGenreSort, (country, hip_hop, pop, jazz, classical, rock) = z3.EnumSort('MusicGenre', ['country', 'hip_hop', 'pop', 'jazz', 'classical', 'rock'])
    HobbySort, (cooking, painting, photography, woodworking, gardening, knitting) = z3.EnumSort('Hobby', ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting'])

    # Create arrays for attributes
    names = [z3.Const(f'name_{i}', NameSort) for i in range(n_houses)]
    styles = [z3.Const(f'style_{i}', HouseStyleSort) for i in range(n_houses)]
    genres = [z3.Const(f'genre_{i}', MusicGenreSort) for i in range(n_houses)]
    hobbies = [z3.Const(f'hobby_{i}', HobbySort) for i in range(n_houses)]

    # Uniqueness constraints
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(styles))
    solver.add(z3.Distinct(genres))
    solver.add(z3.Distinct(hobbies))

    # Clue 1: Rock music in fifth house
    solver.add(genres[4] == rock)

    # Clue 2: Classical and woodworking are adjacent
    for i in range(n_houses - 1):
        solver.add(z3.Or(
            z3.And(genres[i] == classical, hobbies[i+1] == woodworking),
            z3.And(genres[i+1] == classical, hobbies[i] == woodworking)
        ))

    # Clue 3: Mediterranean style implies hip-hop music
    for i in range(n_houses):
        solver.add(z3.Implies(styles[i] == mediterranean, genres[i] == hip_hop))

    # Clue 4: Two houses between Arnold and Victorian house
    # Positions: 0 and 3, 1 and 4, 2 and 5
    solver.add(z3.Or(
        z3.And(names[0] == Arnold, styles[3] == victorian),
        z3.And(names[1] == Arnold, styles[4] == victorian),
        z3.And(names[2] == Arnold, styles[5] == victorian),
        z3.And(names[3] == Arnold, styles[0] == victorian),
        z3.And(names[4] == Arnold, styles[1] == victorian),
        z3.And(names[5] == Arnold, styles[2] == victorian)
    ))

    # Clue 5: Jazz directly left of Eric
    for i in range(n_houses - 1):
        solver.add(z3.Implies(genres[i] == jazz, names[i+1] == Eric))
    for i in range(1, n_houses):
        solver.add(z3.Implies(names[i] == Eric, genres[i-1] == jazz))

    # Clue 6: Hip-hop left of knitting
    hip_hop_pos = z3.Int('hip_hop_pos')
    knitting_pos = z3.Int('knitting_pos')
    solver.add(hip_hop_pos >= 0, hip_hop_pos < n_houses)
    solver.add(knitting_pos >= 0, knitting_pos < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(genres[i] == hip_hop, hip_hop_pos == i))
        solver.add(z3.Implies(hobbies[i] == knitting, knitting_pos == i))
    solver.add(hip_hop_pos < knitting_pos)

    # Clue 7: Carol loves hip-hop
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == Carol, genres[i] == hip_hop))

    # Clue 8: Craftsman style is Arnold
    for i in range(n_houses):
        solver.add(z3.Implies(styles[i] == craftsman, names[i] == Arnold))

    # Clue 9: Ranch style is Eric
    for i in range(n_houses):
        solver.add(z3.Implies(styles[i] == ranch, names[i] == Eric))

    # Clue 10: Woodworking in Victorian house
    for i in range(n_houses):
        solver.add(z3.Implies(hobbies[i] == woodworking, styles[i] == victorian))

    # Clue 11: Country music in first house
    solver.add(genres[0] == country)

    # Clue 12: One house between painting and colonial style
    painting_pos = z3.Int('painting_pos')
    colonial_pos = z3.Int('colonial_pos')
    solver.add(painting_pos >= 0, painting_pos < n_houses)
    solver.add(colonial_pos >= 0, colonial_pos < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(hobbies[i] == painting, painting_pos == i))
        solver.add(z3.Implies(styles[i] == colonial, colonial_pos == i))
    solver.add(z3.Or(
        colonial_pos == painting_pos + 2,
        colonial_pos == painting_pos - 2
    ))

    # Clue 13: Alice is photography enthusiast
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == Alice, hobbies[i] == photography))

    # Clue 14: Eric enjoys gardening
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == Eric, hobbies[i] == gardening))

    # Clue 15: Bob in third house
    solver.add(names[2] == Bob)

    # Check and output solution
    if solver.check() == z3.sat:
        model = solver.model()
        header = ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"]
        rows = []
        for i in range(n_houses):
            name_val = model.eval(names[i])
            style_val = model.eval(styles[i])
            genre_val = model.eval(genres[i])
            hobby_val = model.eval(hobbies[i])
            rows.append([str(i+1), str(name_val), str(style_val), str(genre_val), str(hobby_val)])
        print(json.dumps({"solution": {"header": header, "rows": rows}}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()