import json
from z3 import Int, Solver, And, Distinct, Abs

def main():
    solver = Solver()

    # Define house variables for persons
    Arnold = Int('Arnold')
    Eric = Int('Eric')
    Peter = Int('Peter')
    Alice = Int('Alice')

    solver.add(And(Arnold >= 1, Arnold <= 4))
    solver.add(And(Eric >= 1, Eric <= 4))
    solver.add(And(Peter >= 1, Peter <= 4))
    solver.add(And(Alice >= 1, Alice <= 4))
    solver.add(Distinct(Arnold, Eric, Peter, Alice))

    # Define house variables for occupations
    doctor = Int('doctor')
    engineer = Int('engineer')
    artist = Int('artist')
    teacher = Int('teacher')

    solver.add(And(doctor >= 1, doctor <= 4))
    solver.add(And(engineer >= 1, engineer <= 4))
    solver.add(And(artist >= 1, artist <= 4))
    solver.add(And(teacher >= 1, teacher <= 4))
    solver.add(Distinct(doctor, engineer, artist, teacher))

    # Clue 1: There are two houses between Eric and Peter.
    solver.add(Abs(Eric - Peter) == 3)

    # Clue 2: The person who is a teacher is Peter.
    solver.add(teacher == Peter)

    # Clue 3: Peter is not in the first house.
    solver.add(Peter != 1)

    # Clue 4: There is one house between the person who is a doctor and Alice.
    solver.add(Abs(doctor - Alice) == 2)

    # Clue 5: The person who is an artist is Alice.
    solver.add(artist == Alice)

    if solver.check() == 'sat' or solver.check():
        model = solver.model()

        # Mapping of house number to person name
        person_mapping = {}
        for name, var in [("Arnold", Arnold), ("Eric", Eric), ("Peter", Peter), ("Alice", Alice)]:
            house_num = model.evaluate(var).as_long()
            person_mapping[house_num] = name

        # Mapping of house number to occupation
        occupation_mapping = {}
        for occ, var in [("doctor", doctor), ("engineer", engineer), ("artist", artist), ("teacher", teacher)]:
            house_num = model.evaluate(var).as_long()
            occupation_mapping[house_num] = occ

        rows = []
        for house in range(1, 5):
            name = person_mapping.get(house, "")
            occ = occupation_mapping.get(house, "")
            rows.append([str(house), name, occ])

        result = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == '__main__':
    main()