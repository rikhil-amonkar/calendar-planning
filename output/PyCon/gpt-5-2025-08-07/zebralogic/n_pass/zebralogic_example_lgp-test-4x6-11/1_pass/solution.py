import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    bookgenres = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    musicgenres = ["pop", "rock", "classical", "jazz"]

    problem = Problem()

    # Add variables
    for n in names:
        problem.addVariable(n, houses)
    for h in hobbies:
        problem.addVariable(h, houses)
    for a in animals:
        problem.addVariable(a, houses)
    for b in bookgenres:
        problem.addVariable(b, houses)
    for d in birthdays:
        problem.addVariable(d, houses)
    for m in musicgenres:
        problem.addVariable(m, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hobbies)
    problem.addConstraint(AllDifferentConstraint(), animals)
    problem.addConstraint(AllDifferentConstraint(), bookgenres)
    problem.addConstraint(AllDifferentConstraint(), birthdays)
    problem.addConstraint(AllDifferentConstraint(), musicgenres)

    # Clues:
    # 1. The person who loves cooking is the person who loves romance books.
    problem.addConstraint(lambda c, r: c == r, ("cooking", "romance"))

    # 2. The person whose birthday is in February is the person who loves pop music.
    problem.addConstraint(lambda feb, pop: feb == pop, ("feb", "pop"))

    # 3. Eric is not in the second house.
    problem.addConstraint(lambda e: e != 2, ("Eric",))

    # 4. The person who loves romance books is not in the fourth house.
    problem.addConstraint(lambda r: r != 4, ("romance",))

    # 5. The person whose birthday is in February is the fish enthusiast.
    problem.addConstraint(lambda feb, fish: feb == fish, ("feb", "fish"))

    # 6. Alice is somewhere to the right of the person who loves fantasy books.
    problem.addConstraint(lambda alice, fantasy: alice > fantasy, ("Alice", "fantasy"))

    # 7. The person who keeps horses is the person who loves rock music.
    problem.addConstraint(lambda horse, rock: horse == rock, ("horse", "rock"))

    # 8. The person who enjoys gardening is the person whose birthday is in April.
    problem.addConstraint(lambda gardening, april: gardening == april, ("gardening", "april"))

    # 9. The person who loves jazz music is the person who loves cooking.
    problem.addConstraint(lambda jazz, cooking: jazz == cooking, ("jazz", "cooking"))

    # 10. The person who loves rock music is the person who loves mystery books.
    problem.addConstraint(lambda rock, mystery: rock == mystery, ("rock", "mystery"))

    # 11. The person who paints as a hobby is directly left of the person who loves romance books.
    problem.addConstraint(lambda painting, romance: painting == romance - 1, ("painting", "romance"))

    # 12. Peter is the person who loves pop music.
    problem.addConstraint(lambda Peter, pop: Peter == pop, ("Peter", "pop"))

    # 13. The person who enjoys gardening is Arnold.
    problem.addConstraint(lambda gardening, Arnold: gardening == Arnold, ("gardening", "Arnold"))

    # 14. The person who loves rock music is directly left of the person whose birthday is in January.
    problem.addConstraint(lambda rock, jan: rock == jan - 1, ("rock", "jan"))

    # 15. The person who loves cooking is not in the third house.
    problem.addConstraint(lambda cooking: cooking != 3, ("cooking",))

    # 16. The cat lover is somewhere to the right of the person who keeps horses.
    problem.addConstraint(lambda cat, horse: cat > horse, ("cat", "horse"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build output rows per house
    rows = []
    for h in houses:
        name_val = next(n for n in names if sol[n] == h)
        hobby_val = next(x for x in hobbies if sol[x] == h)
        animal_val = next(x for x in animals if sol[x] == h)
        book_val = next(x for x in bookgenres if sol[x] == h)
        bday_val = next(x for x in birthdays if sol[x] == h)
        music_val = next(x for x in musicgenres if sol[x] == h)

        rows.append([str(h), name_val, hobby_val, animal_val, book_val, bday_val, music_val])

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    output = solve_puzzle()
    print(json.dumps(output, ensure_ascii=False))