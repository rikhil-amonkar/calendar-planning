from z3 import *
import json

def main():
    s = Solver()

    # We assign integer values to each attribute:
    # Names: 0 -> Peter, 1 -> Eric, 2 -> Arnold
    # Smoothies: 0 -> cherry, 1 -> desert, 2 -> watermelon
    # Books: 0 -> mystery, 1 -> science fiction, 2 -> romance

    # Create variables for each house (houses are numbered 1, 2, 3)
    name1, name2, name3 = Ints('name1 name2 name3')
    smoothie1, smoothie2, smoothie3 = Ints('smoothie1 smoothie2 smoothie3')
    book1, book2, book3 = Ints('book1 book2 book3')

    houses = [name1, name2, name3]
    smoothies = [smoothie1, smoothie2, smoothie3]
    books = [book1, book2, book3]

    # Domain constraints: all variables must be in {0,1,2}.
    for var in houses + smoothies + books:
        s.add(var >= 0, var < 3)

    # Each attribute category is all-different.
    s.add(Distinct(name1, name2, name3))
    s.add(Distinct(smoothie1, smoothie2, smoothie3))
    s.add(Distinct(book1, book2, book3))

    # Clue 5: Peter is in the first house.
    # Peter is represented by 0.
    s.add(name1 == 0)

    # Clue 2: Arnold is the person who loves mystery books.
    # Arnold = 2, mystery = 0.
    s.add(Implies(name1 == 2, book1 == 0))
    s.add(Implies(name2 == 2, book2 == 0))
    s.add(Implies(name3 == 2, book3 == 0))

    # Clue 3: The person who loves science fiction books (1) is not in the first house.
    s.add(book1 != 1)

    # Clue 4: The Desert smoothie lover (1) is directly left of the person who loves mystery books (0).
    # Thus, mystery cannot be in house 1.
    s.add(book1 != 0)
    # If house2 has mystery then house1 must have desert.
    s.add(Implies(book2 == 0, smoothie1 == 1))
    # If house3 has mystery then house2 must have desert.
    s.add(Implies(book3 == 0, smoothie2 == 1))

    # Clue 1: The person who likes Cherry smoothies (0) is somewhere to the left of the person who loves mystery books (0).
    # If mystery is in house2 then house1 must be cherry.
    s.add(Implies(book2 == 0, smoothie1 == 0))
    # If mystery is in house3 then either house1 or house2 must be cherry.
    s.add(Implies(book3 == 0, Or(smoothie1 == 0, smoothie2 == 0)))

    # Check for a solution.
    if s.check() == sat:
        m = s.model()

        # Mapping back from numbers to strings.
        names_map = {0: "Peter", 1: "Eric", 2: "Arnold"}
        smoothies_map = {0: "cherry", 1: "desert", 2: "watermelon"}
        books_map = {0: "mystery", 1: "science fiction", 2: "romance"}

        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "BookGenre"],
                "rows": [
                    ["1", names_map[m[name1].as_long()], smoothies_map[m[smoothie1].as_long()], books_map[m[book1].as_long()]],
                    ["2", names_map[m[name2].as_long()], smoothies_map[m[smoothie2].as_long()], books_map[m[book2].as_long()]],
                    ["3", names_map[m[name3].as_long()], smoothies_map[m[smoothie3].as_long()], books_map[m[book3].as_long()]]
                ]
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()