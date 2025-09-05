import json
import itertools

def solve():
    # Houses are indexed 0..2 but will be output as "1","2","3"
    houses = [0, 1, 2]

    # Attributes (as given)
    Names = ['Peter', 'Arnold', 'Eric']
    BookGenres = ['science fiction', 'mystery', 'romance']
    Smoothies = ['watermelon', 'desert', 'cherry']
    Birthdays = ['april', 'jan', 'sept']
    Heights = ['average', 'very short', 'short']

    def idx_of(lst, value):
        return lst.index(value)

    solutions = []

    # Iterate over all possible assignments (permutations) for each category
    for names_perm in itertools.permutations(Names):
        # Clue 7: Eric is in the first house.
        if names_perm[0] != 'Eric':
            continue

        for books_perm in itertools.permutations(BookGenres):
            # Clue 2: Arnold is the person who loves mystery books.
            if books_perm[idx_of(names_perm, 'Arnold')] != 'mystery':
                continue

            # Clue 5: The person who loves mystery books is the person whose birthday is in September.
            # We'll apply this after picking birthdays

            for smoothies_perm in itertools.permutations(Smoothies):
                # Clue 1: The person who likes Cherry smoothies is not in the second house.
                if smoothies_perm[1] == 'cherry':
                    continue

                # Clue 9: The Watermelon smoothie lover is Eric.
                if idx_of(smoothies_perm, 'watermelon') != idx_of(names_perm, 'Eric'):
                    continue

                for birthdays_perm in itertools.permutations(Birthdays):
                    # Clue 3: The person whose birthday is in January is not in the first house.
                    if birthdays_perm[0] == 'jan':
                        continue

                    # Clue 5: Mystery lover has September birthday.
                    if birthdays_perm[idx_of(books_perm, 'mystery')] != 'sept':
                        continue

                    for heights_perm in itertools.permutations(Heights):
                        # Clue 6: The person who has an average height is the Desert smoothie lover.
                        if idx_of(heights_perm, 'average') != idx_of(smoothies_perm, 'desert'):
                            continue

                        # Clue 4: The person who is very short is the person who loves romance books.
                        if idx_of(heights_perm, 'very short') != idx_of(books_perm, 'romance'):
                            continue

                        # Clue 8: The Watermelon smoothie lover is the person who is short.
                        if idx_of(smoothies_perm, 'watermelon') != idx_of(heights_perm, 'short'):
                            continue

                        # All constraints satisfied; record solution
                        solution_rows = []
                        for h in houses:
                            row = [
                                str(h + 1),
                                names_perm[h],
                                books_perm[h],
                                smoothies_perm[h],
                                birthdays_perm[h],
                                heights_perm[h],
                            ]
                            solution_rows.append(row)
                        solutions.append(solution_rows)

    # Prepare JSON output (use the first solution if multiple, though puzzle should have a unique one)
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": solutions[0] if solutions else []
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve()