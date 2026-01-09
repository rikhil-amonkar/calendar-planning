import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ["Eric", "Alice", "Peter", "Arnold"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Sports = ["soccer", "tennis", "basketball", "swimming"]
    Cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    Flowers = ["daffodils", "roses", "lilies", "carnations"]

    problem = Problem()

    # Create variables: each attribute value maps to a house position (1..4)
    for n in Names:
        problem.addVariable(n, houses)
    for s in Smoothies:
        problem.addVariable(s, houses)
    for sp in Sports:
        problem.addVariable(sp, houses)
    for c in Cars:
        problem.addVariable(c, houses)
    for f in Flowers:
        problem.addVariable(f, houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Smoothies)
    problem.addConstraint(AllDifferentConstraint(), Sports)
    problem.addConstraint(AllDifferentConstraint(), Cars)
    problem.addConstraint(AllDifferentConstraint(), Flowers)

    # Clues:

    # 1. Tesla Model 3 owner loves roses.
    problem.addConstraint(lambda a, b: a == b, ("tesla model 3", "roses"))

    # 2. Peter is the Dragonfruit smoothie lover.
    problem.addConstraint(lambda a, b: a == b, ("Peter", "dragonfruit"))

    # 3. Desert smoothie lover owns a Toyota Camry.
    problem.addConstraint(lambda a, b: a == b, ("desert", "toyota camry"))

    # 4. Tennis is in the first house.
    problem.addConstraint(lambda a: a == 1, ("tennis",))

    # 5. Toyota Camry and basketball are next to each other.
    problem.addConstraint(lambda a, b: abs(a - b) == 1, ("toyota camry", "basketball"))

    # 6. Arnold loves basketball.
    problem.addConstraint(lambda a, b: a == b, ("Arnold", "basketball"))

    # 7. Honda Civic owner loves daffodils.
    problem.addConstraint(lambda a, b: a == b, ("honda civic", "daffodils"))

    # 8. Eric loves roses.
    problem.addConstraint(lambda a, b: a == b, ("Eric", "roses"))

    # 9. Watermelon smoothie lover is not in the first house.
    problem.addConstraint(lambda a: a != 1, ("watermelon",))

    # 10. Honda Civic is somewhere to the right of the Desert smoothie lover.
    problem.addConstraint(lambda honda, desert: honda > desert, ("honda civic", "desert"))

    # 11. Basketball lover loves lilies.
    problem.addConstraint(lambda a, b: a == b, ("basketball", "lilies"))

    # 12. Tennis and soccer are next to each other.
    problem.addConstraint(lambda t, s: abs(t - s) == 1, ("tennis", "soccer"))

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Expecting a unique solution; pick the first if multiple
    sol = solutions[0]

    # Build reverse lookups: house -> attribute value
    def invert(values):
        return {sol[val]: val for val in values}

    name_at = invert(Names)
    smoothie_at = invert(Smoothies)
    sport_at = invert(Sports)
    car_at = invert(Cars)
    flower_at = invert(Flowers)

    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            name_at[h],
            smoothie_at[h],
            sport_at[h],
            car_at[h],
            flower_at[h],
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    solve_puzzle()