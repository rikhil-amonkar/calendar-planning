from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 2

    # Create Z3 integer variables for each attribute for each house.
    names = [Int(f"name{i}") for i in range(num_houses)]
    occupations = [Int(f"occ{i}") for i in range(num_houses)]
    birthdays = [Int(f"birth{i}") for i in range(num_houses)]
    house_styles = [Int(f"style{i}") for i in range(num_houses)]
    heights = [Int(f"height{i}") for i in range(num_houses)]
    cigars = [Int(f"cigar{i}") for i in range(num_houses)]

    # Define domain for each variable (0 or 1)
    all_vars = names + occupations + birthdays + house_styles + heights + cigars
    for var in all_vars:
        solver.add(var >= 0, var < 2)

    # Enforce that each attribute is unique across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(occupations))
    solver.add(Distinct(birthdays))
    solver.add(Distinct(house_styles))
    solver.add(Distinct(heights))
    solver.add(Distinct(cigars))

    # Mapping:
    # For Name: 0 -> "Arnold", 1 -> "Eric"
    # For Occupation: 0 -> "engineer", 1 -> "doctor"
    # For Birthday: 0 -> "april", 1 -> "sept"
    # For HouseStyle: 0 -> "victorian", 1 -> "colonial"
    # For Height: 0 -> "very short", 1 -> "short"
    # For Cigar: 0 -> "prince", 1 -> "pall mall"

    # Clue 1: The person who is an engineer is in the first house.
    # (Engineer is mapped to 0 in Occupations)
    solver.add(occupations[0] == 0)

    # Clue 2: The person whose birthday is in April (0) and the person who is a doctor (1) are next to each other.
    # With 2 houses, they must occupy different houses.
    solver.add(
        Or(
            And(birthdays[0] == 0, occupations[1] == 1),
            And(birthdays[1] == 0, occupations[0] == 1)
        )
    )

    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
    # Colonial-style is mapped to 1; thus if a house is colonial then the occupation must be engineer (0), and vice versa.
    for i in range(num_houses):
        solver.add(house_styles[i] == If(occupations[i] == 0, 1, 0))

    # Clue 4: The person who is very short is the person who is an engineer.
    # "Very short" is mapped to 0; so if a person is an engineer then they are very short, otherwise they are short (1).
    for i in range(num_houses):
        solver.add(heights[i] == If(occupations[i] == 0, 0, 1))

    # Clue 5: The person who is short is the person partial to Pall Mall.
    # "Short" is mapped to 1 and "Pall Mall" is mapped to 1.
    for i in range(num_houses):
        solver.add(cigars[i] == If(heights[i] == 1, 1, 0))

    # Clue 6: The person who is an engineer is Eric.
    # If the occupation is engineer (0) then the name must be Eric (1).
    for i in range(num_houses):
        solver.add(Implies(occupations[i] == 0, names[i] == 1))

    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()

        # Define mapping dictionaries for output.
        name_map = {0: "Arnold", 1: "Eric"}
        occupation_map = {0: "engineer", 1: "doctor"}
        birthday_map = {0: "april", 1: "sept"}
        house_style_map = {0: "victorian", 1: "colonial"}
        height_map = {0: "very short", 1: "short"}
        cigar_map = {0: "prince", 1: "pall mall"}

        # Build rows for each house.
        rows = []
        for i in range(num_houses):
            row = [
                str(i + 1),
                name_map[model[names[i]].as_long()],
                occupation_map[model[occupations[i]].as_long()],
                birthday_map[model[birthdays[i]].as_long()],
                house_style_map[model[house_styles[i]].as_long()],
                height_map[model[heights[i]].as_long()],
                cigar_map[model[cigars[i]].as_long()]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()