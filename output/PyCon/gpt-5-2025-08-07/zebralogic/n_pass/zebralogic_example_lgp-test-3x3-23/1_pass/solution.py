import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Houses are positions 1..3 from left to right
    positions = [1, 2, 3]

    # Attributes
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Set up the constraint problem
    problem = Problem()

    # Add variables for each attribute value with domains as house positions
    for v in names + occupations + hobbies:
        problem.addVariable(v, positions)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), occupations)
    problem.addConstraint(AllDifferentConstraint(), hobbies)

    # Clue 1: The person who is a doctor and Eric are next to each other.
    problem.addConstraint(lambda doctor, Eric: abs(doctor - Eric) == 1, ("doctor", "Eric"))

    # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
    problem.addConstraint(lambda cooking, teacher: cooking + 1 == teacher, ("cooking", "teacher"))

    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    problem.addConstraint(lambda doctor, gardening: doctor > gardening, ("doctor", "gardening"))

    # Clue 4: The photography enthusiast is the person who is a teacher.
    problem.addConstraint(lambda photography, teacher: photography == teacher, ("photography", "teacher"))

    # Clue 5: The person who is an engineer is Peter.
    problem.addConstraint(lambda engineer, Peter: engineer == Peter, ("engineer", "Peter"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assuming a unique solution for this puzzle
    sol = solutions[0]

    # Build mappings from position to attributes
    name_by_pos = {sol[name]: name for name in names}
    occupation_by_pos = {sol[occ]: occ for occ in occupations}
    hobby_by_pos = {sol[hobby]: hobby for hobby in hobbies}

    # Prepare rows in house order 1..3
    rows = []
    for pos in positions:
        rows.append([
            str(pos),
            name_by_pos[pos],
            occupation_by_pos[pos],
            hobby_by_pos[pos]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve_puzzle()