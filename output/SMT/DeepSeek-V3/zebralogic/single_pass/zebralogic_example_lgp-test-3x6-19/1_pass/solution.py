from z3 import *

def solve_puzzle():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the attributes
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    genres = ['science fiction', 'romance', 'mystery']
    phones = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

    # Create dictionaries to hold the variables for each house
    name = {house: Int(f'name_{house}') for house in houses}
    cigar = {house: Int(f'cigar_{house}') for house in houses}
    animal = {house: Int(f'animal_{house}') for house in houses}
    child = {house: Int(f'child_{house}') for house in houses}
    genre = {house: Int(f'genre_{house}') for house in houses}
    phone = {house: Int(f'phone_{house}') for house in houses}

    # Add constraints to ensure each attribute is unique within its category
    for house in houses:
        s.add(And(name[house] >= 0, name[house] < len(names)))
        s.add(And(cigar[house] >= 0, cigar[house] < len(cigars)))
        s.add(And(animal[house] >= 0, animal[house] < len(animals)))
        s.add(And(child[house] >= 0, child[house] < len(children)))
        s.add(And(genre[house] >= 0, genre[house] < len(genres)))
        s.add(And(phone[house] >= 0, phone[house] < len(phones)))

    s.add(Distinct([name[house] for house in houses]))
    s.add(Distinct([cigar[house] for house in houses]))
    s.add(Distinct([animal[house] for house in houses]))
    s.add(Distinct([child[house] for house in houses]))
    s.add(Distinct([genre[house] for house in houses]))
    s.add(Distinct([phone[house] for house in houses]))

    # Add constraints based on the clues
    # Clue 3: The person partial to Pall Mall is in the second house.
    s.add(cigar[2] == cigars.index('pall mall'))

    # Clue 10: The person who loves science fiction books is in the third house.
    s.add(genre[3] == genres.index('science fiction'))

    # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    s.add(phone[3] == phones.index('samsung galaxy s21'))

    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    # Since Samsung is in house 3, iPhone must be in house 2.
    s.add(phone[2] == phones.index('iphone 13'))

    # Clue 7: The person's child is named Fred is directly left of Arnold.
    # This means Fred's child is in house X, Arnold is in house X+1.
    # Possible positions: Fred in 1, Arnold in 2 or Fred in 2, Arnold in 3.
    # But Arnold cannot be in 3 because house 3's name is not yet assigned, but let's see.
    # We'll model this as: child[house] == Fred and name[house+1] == Arnold.
    s.add(Or(
        And(child[1] == children.index('Fred'), name[2] == names.index('Arnold')),
        And(child[2] == children.index('Fred'), name[3] == names.index('Arnold'))
    ))

    # Clue 1: The person who loves mystery books is the person's child is named Fred.
    # So genre[house] == mystery implies child[house] == Fred.
    for house in houses:
        s.add(Implies(genre[house] == genres.index('mystery'), child[house] == children.index('Fred')))

    # Clue 11: The person who loves mystery books is not in the second house.
    s.add(genre[2] != genres.index('mystery'))

    # Clue 4: The person who keeps horses is the person's child is named Meredith.
    for house in houses:
        s.add(Implies(animal[house] == animals.index('horse'), child[house] == children.index('Meredith')))

    # Clue 5: The person's child is named Bella is the Prince smoker.
    for house in houses:
        s.add(Implies(child[house] == children.index('Bella'), cigar[house] == cigars.index('prince')))

    # Clue 2: The cat lover is Eric.
    for house in houses:
        s.add(Implies(animal[house] == animals.index('cat'), name[house] == names.index('Eric')))

    # Clue 8: Peter is somewhere to the left of Eric.
    # This means Peter is in a house with a lower number than Eric.
    # We'll find the house numbers for Peter and Eric and ensure Peter's is less.
    peter_pos = Int('peter_pos')
    eric_pos = Int('eric_pos')
    s.add(peter_pos >= 1)
    s.add(peter_pos <= 3)
    s.add(eric_pos >= 1)
    s.add(eric_pos <= 3)
    s.add(peter_pos < eric_pos)
    for house in houses:
        s.add(Implies(name[house] == names.index('Peter'), peter_pos == house))
        s.add(Implies(name[house] == names.index('Eric'), eric_pos == house))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": []
            }
        }
        for house in houses:
            row = [
                str(house),
                names[m.evaluate(name[house]).as_long()],
                cigars[m.evaluate(cigar[house]).as_long()],
                animals[m.evaluate(animal[house]).as_long()],
                children[m.evaluate(child[house]).as_long()],
                genres[m.evaluate(genre[house]).as_long()],
                phones[m.evaluate(phone[house]).as_long()]
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Print the solution as JSON
import json
solution = solve_puzzle()
print(json.dumps(solution, indent=2))