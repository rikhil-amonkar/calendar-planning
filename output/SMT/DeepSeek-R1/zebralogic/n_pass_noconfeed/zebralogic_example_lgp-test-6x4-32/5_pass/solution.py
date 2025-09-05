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

    # Clue 2: Classical music listener is woodworking enthusiast (same house)
    for i in range(n_houses):
        solver.add(z3.Implies(genres[i] == classical, hobbies[i] == woodworking))
        solver.add(z3.Implies(hobbies[i] == woodworking, genres[i] == classical))

    # Clue 3: Mediterranean style implies hip-hop music
    for i in range(n_houses):
        solver.add(z3.Implies(styles[i] == mediterranean, genres[i] == hip_hop))

    # Clue 4: Two houses between Arnold and Victorian house
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
    for i in range(n_houses):
        for j in range(n_houses):
            if i < j:
                solver.add(z3.Implies(genres[i] == hip_hop, hobbies[j] != knitting))
            else:
                solver.add(z3.Implies(genres[i] == hip_hop, hobbies[j] != knitting))

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
    for i in range(n_houses):
        for j in range(n_houses):
            if abs(i - j) == 2:
                solver.add(z3.Implies(hobbies[i] == painting, styles[j] == colonial))
                solver.add(z3.Implies(styles[i] == colonial, hobbies[j] == painting))

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