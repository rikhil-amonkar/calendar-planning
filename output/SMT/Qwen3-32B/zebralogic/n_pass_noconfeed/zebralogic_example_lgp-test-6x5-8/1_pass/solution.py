from z3 import *
import json

def solve_puzzle():
    # Define EnumSorts for each category
    Name, (Arnold, Peter, Bob, Eric, Carol, Alice) = EnumSort('Name', ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice'])
    Animal, (horse, rabbit, fish, cat, bird, dog) = EnumSort('Animal', ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog'])
    Occupation, (engineer, nurse, lawyer, teacher, artist, doctor) = EnumSort('Occupation', ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor'])
    Sport, (basketball, volleyball, soccer, tennis, baseball, swimming) = EnumSort('Sport', ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming'])
    Height, (average, tall, short, very_short, very_tall, super_tall) = EnumSort('Height', ['average', 'tall', 'short', 'very short', 'very tall', 'super tall'])

    # Create variables for each house (0-based index)
    solver = Solver()

    names = [Const(f'Name_{i}', Name) for i in range(6)]
    animals = [Const(f'Animal_{i}', Animal) for i in range(6)]
    occupations = [Const(f'Occupation_{i}', Occupation) for i in range(6)]
    sports = [Const(f'Sport_{i}', Sport) for i in range(6)]
    heights = [Const(f'Height_{i}', Height) for i in range(6)]

    # Add distinctness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(animals))
    solver.add(Distinct(occupations))
    solver.add(Distinct(sports))
    solver.add(Distinct(heights))

    # Clue 1: Engineer is dog owner
    for i in range(6):
        solver.add(Implies(occupations[i] == engineer, animals[i] == dog))

    # Clue 2: Average height is left of short
    i_avg = Int('i_avg')
    i_short = Int('i_short')
    for k in range(6):
        solver.add((heights[k] == average) == (i_avg == k))
    for k in range(6):
        solver.add((heights[k] == short) == (i_short == k))
    solver.add(i_avg < i_short)

    # Clue 3: Average height directly left of rabbit owner
    i_rabbit = Int('i_rabbit')
    for k in range(6):
        solver.add((animals[k] == rabbit) == (i_rabbit == k))
    solver.add(i_avg + 1 == i_rabbit)

    # Clue 4: Tall is left of very short
    i_tall = Int('i_tall')
    i_very_short = Int('i_very_short')
    for k in range(6):
        solver.add((heights[k] == tall) == (i_tall == k))
    for k in range(6):
        solver.add((heights[k] == very_short) == (i_very_short == k))
    solver.add(i_tall < i_very_short)

    # Clue 5: Arnold is cat lover
    i_arnold = Int('i_arnold')
    for k in range(6):
        solver.add((names[k] == Arnold) == (i_arnold == k))
    for i in range(6):
        solver.add(Implies(i_arnold == i, animals[i] == cat))

    # Clue 6: Horse owner is teacher
    for i in range(6):
        solver.add(Implies(animals[i] == horse, occupations[i] == teacher))

    # Clue 7: Carol loves soccer
    for i in range(6):
        solver.add(Implies(names[i] == Carol, sports[i] == soccer))

    # Clue 8: Tall loves volleyball
    for i in range(6):
        solver.add(Implies(heights[i] == tall, sports[i] == volleyball))

    # Clue 9: Lawyer in 5th house (index 4)
    solver.add(occupations[4] == lawyer)

    # Clue 10: Tennis lover is teacher
    for i in range(6):
        solver.add(Implies(sports[i] == tennis, occupations[i] == teacher))

    # Clue 11: Average height loves swimming
    for i in range(6):
        solver.add(Implies(heights[i] == average, sports[i] == swimming))

    # Clue 12: Baseball directly left of engineer
    i_baseball = Int('i_baseball')
    i_engineer = Int('i_engineer')
    for k in range(6):
        solver.add((sports[k] == baseball) == (i_baseball == k))
    for k in range(6):
        solver.add((occupations[k] == engineer) == (i_engineer == k))
    solver.add(i_baseball + 1 == i_engineer)

    # Clue 13: Peter is nurse
    for i in range(6):
        solver.add(Implies(names[i] == Peter, occupations[i] == nurse))

    # Clue 14: Bob is right of artist
    i_bob = Int('i_bob')
    i_artist = Int('i_artist')
    for k in range(6):
        solver.add((names[k] == Bob) == (i_bob == k))
    for k in range(6):
        solver.add((occupations[k] == artist) == (i_artist == k))
    solver.add(i_bob > i_artist)

    # Clue 15: Teacher directly left of soccer
    i_teacher = Int('i_teacher')
    i_soccer = Int('i_soccer')
    for k in range(6):
        solver.add((occupations[k] == teacher) == (i_teacher == k))
    for k in range(6):
        solver.add((sports[k] == soccer) == (i_soccer == k))
    solver.add(i_teacher + 1 == i_soccer)

    # Clue 16: Rabbit owner is Alice
    for i in range(6):
        solver.add(Implies(animals[i] == rabbit, names[i] == Alice))

    # Clue 17: Fish enthusiast is Carol
    for i in range(6):
        solver.add(Implies(animals[i] == fish, names[i] == Carol))

    # Clue 18: Baseball in first house
    solver.add(sports[0] == baseball)

    # Clue 19: Cat lover (Arnold) is right of very short
    solver.add(i_arnold > i_very_short)

    # Clue 20: Super tall in 5th house
    solver.add(heights[4] == super_tall)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Generate the solution rows
        rows = []
        for i in range(6):
            house_num = i + 1
            name = model.evaluate(names[i])
            animal = model.evaluate(animals[i])
            occupation = model.evaluate(occupations[i])
            sport = model.evaluate(sports[i])
            height = model.evaluate(heights[i])
            rows.append([str(house_num), str(name), str(animal), str(occupation), str(sport), str(height)])
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": rows
            }
        }
        return solution
    else:
        return {"error": "No solution found"}

# Generate the JSON output
solution = solve_puzzle()
print(json.dumps(solution, indent=2))