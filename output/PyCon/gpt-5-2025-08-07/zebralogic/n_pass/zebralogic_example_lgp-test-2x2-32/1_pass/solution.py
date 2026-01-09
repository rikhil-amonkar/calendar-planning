import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the puzzle parameters
    houses = [1, 2]  # House positions from left (1) to right (2)
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]

    # Initialize the problem
    problem = Problem()

    # Create variable names
    name_vars = {name: f"Name_{name}" for name in names}
    genre_vars = {genre: f"Genre_{genre.replace(' ', '_')}" for genre in genres}

    # Add variables with domains (house positions)
    for var in name_vars.values():
        problem.addVariable(var, houses)
    for var in genre_vars.values():
        problem.addVariable(var, houses)

    # Add uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), list(name_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(genre_vars.values()))

    # Clue: Eric is directly left of the person who loves mystery books
    problem.addConstraint(
        lambda eric_pos, mystery_pos: eric_pos + 1 == mystery_pos,
        [name_vars["Eric"], genre_vars["mystery"]]
    )

    # Solve the problem
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    sol = solutions[0]

    # Build mappings from house to attributes
    pos_to_name = {sol[name_vars[name]]: name for name in names}
    pos_to_genre = {sol[genre_vars[genre]]: genre for genre in genres}

    # Prepare the JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": []
        }
    }

    for h in sorted(houses):
        output["solution"]["rows"].append([
            str(h),
            pos_to_name[h],
            pos_to_genre[h]
        ])

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()