import itertools
import json

def solve():
    # Puzzle parameters
    houses = [1, 2, 3]  # left (1) to right (3)
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    books = ["science fiction", "romance", "mystery"]

    solutions = []

    # Iterate over all permutations respecting uniqueness within each category
    for name_perm in itertools.permutations(names):
        # Map house -> name
        name_at = {house: name_perm[house - 1] for house in houses}

        # Clue 5: Peter is in the first house.
        if name_at[1] != "Peter":
            continue

        for book_perm in itertools.permutations(books):
            book_at = {house: book_perm[house - 1] for house in houses}

            # Clue 2: Arnold is the person who loves mystery books.
            # Find Arnold's house and ensure it has 'mystery'
            arnold_house = next(h for h in houses if name_at[h] == "Arnold")
            if book_at[arnold_house] != "mystery":
                continue

            # Clue 3: The person who loves science fiction books is not in the first house.
            if book_at[1] == "science fiction":
                continue

            # Precompute house of mystery for later clues
            house_mystery = next(h for h in houses if book_at[h] == "mystery")

            for smoothie_perm in itertools.permutations(smoothies):
                smoothie_at = {house: smoothie_perm[house - 1] for house in houses}

                # Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
                # So house_desert = house_mystery - 1
                if house_mystery - 1 not in houses:
                    continue
                if smoothie_at[house_mystery - 1] != "desert":
                    continue

                # Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
                house_cherry = next(h for h in houses if smoothie_at[h] == "cherry")
                if not (house_cherry < house_mystery):
                    continue

                # All constraints satisfied; record solution
                solution_rows = []
                for h in houses:
                    solution_rows.append([
                        str(h),
                        name_at[h],
                        smoothie_at[h],
                        book_at[h]
                    ])
                solutions.append(solution_rows)

    # Expect a unique solution; take the first if multiple
    if not solutions:
        raise RuntimeError("No solution found.")
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()