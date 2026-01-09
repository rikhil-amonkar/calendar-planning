import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3]

    # Categories
    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    books = ["science fiction", "romance", "mystery"]
    phones = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Initialize problem
    problem = Problem()

    # Add variables for each attribute value with domain of house positions
    for item in names + cigars + animals + children + books + phones:
        problem.addVariable(item, houses)

    # Each category must be all different
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), cigars)
    problem.addConstraint(AllDifferentConstraint(), animals)
    problem.addConstraint(AllDifferentConstraint(), children)
    problem.addConstraint(AllDifferentConstraint(), books)
    problem.addConstraint(AllDifferentConstraint(), phones)

    # Clues as constraints:

    # 1. The person who loves mystery books is the person's child is named Fred.
    problem.addConstraint(lambda mystery, Fred: mystery == Fred, ("mystery", "Fred"))

    # 2. The cat lover is Eric.
    problem.addConstraint(lambda cat, Eric: cat == Eric, ("cat", "Eric"))

    # 3. The person partial to Pall Mall is in the second house.
    problem.addConstraint(lambda pm: pm == 2, ("pall mall",))

    # 4. The person who keeps horses is the person's child is named Meredith.
    problem.addConstraint(lambda horse, Meredith: horse == Meredith, ("horse", "Meredith"))

    # 5. The person's child is named Bella is the Prince smoker.
    problem.addConstraint(lambda Bella, prince: Bella == prince, ("Bella", "prince"))

    # 6. The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda iphone, s21: iphone + 1 == s21, ("iphone 13", "samsung galaxy s21"))

    # 7. The person's child is named Fred is directly left of Arnold.
    problem.addConstraint(lambda Fred, Arnold: Fred + 1 == Arnold, ("Fred", "Arnold"))

    # 8. Peter is somewhere to the left of Eric.
    problem.addConstraint(lambda Peter, Eric: Peter < Eric, ("Peter", "Eric"))

    # 9. The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda scifi, s21: scifi == s21, ("science fiction", "samsung galaxy s21"))

    # 10. The person who loves science fiction books is in the third house.
    problem.addConstraint(lambda scifi: scifi == 3, ("science fiction",))

    # 11. The person who loves mystery books is not in the second house.
    problem.addConstraint(lambda mystery: mystery != 2, ("mystery",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the puzzle.")

    sol = solutions[0]

    def value_at_house(category_list, house):
        for item in category_list:
            if sol[item] == house:
                return item
        return None

    header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]
    rows = []
    for h in sorted(houses):
        row = [
            str(h),
            value_at_house(names, h),
            value_at_house(cigars, h),
            value_at_house(animals, h),
            value_at_house(children, h),
            value_at_house(books, h),
            value_at_house(phones, h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()