import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define houses and attribute domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    # Initialize problem
    problem = Problem()

    # Add variables for each house and attribute
    for h in houses:
        problem.addVariable(f"Name_{h}", names)
        problem.addVariable(f"FavoriteSport_{h}", sports)
        problem.addVariable(f"Hobby_{h}", hobbies)

    # Uniqueness constraints across houses
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"FavoriteSport_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"Hobby_{h}" for h in houses])

    # Clue 1: The person who enjoys gardening is Arnold (bi-conditional)
    for h in houses:
        problem.addConstraint(
            lambda hobby, name: (hobby != "gardening") or (name == "Arnold"),
            (f"Hobby_{h}", f"Name_{h}")
        )
        problem.addConstraint(
            lambda name, hobby: (name != "Arnold") or (hobby == "gardening"),
            (f"Name_{h}", f"Hobby_{h}")
        )

    # Clue 2: The photography enthusiast is not in the first house
    problem.addConstraint(lambda hobby: hobby != "photography", (f"Hobby_{houses[0]}",))

    # Clue 3: The person who loves soccer is not in the first house
    problem.addConstraint(lambda sport: sport != "soccer", (f"FavoriteSport_{houses[0]}",))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build output JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": []
        }
    }

    for h in sorted(houses):
        row = [
            str(h),
            sol[f"Name_{h}"],
            sol[f"FavoriteSport_{h}"],
            sol[f"Hobby_{h}"]
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()