import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2, 3]  # 0-based indices for houses 1..4

    Names = ['Peter', 'Alice', 'Eric', 'Arnold']
    Hobbies = ['cooking', 'painting', 'gardening', 'photography']
    Animals = ['horse', 'fish', 'cat', 'bird']
    BookGenres = ['fantasy', 'mystery', 'romance', 'science fiction']
    Birthdays = ['april', 'jan', 'sept', 'feb']
    MusicGenres = ['pop', 'rock', 'classical', 'jazz']

    solutions = []

    # Iterate over permutations for BookGenres per house
    for books in permutations(BookGenres):
        # books[i] is the book genre at house i
        pos_romance = books.index('romance')

        # Clue 15: cooking not in the third house -> since cooking=romance, romance not at index 2
        if pos_romance == 2:
            continue
        # Clue 4: romance not in the fourth house -> index 3
        if pos_romance == 3:
            continue
        # Clue 11: painting directly left of romance -> romance cannot be at index 0
        if pos_romance == 0:
            continue
        # At this point pos_romance must be 1
        if pos_romance != 1:
            continue

        # Music permutations
        for music in permutations(MusicGenres):
            # Clue 9 and 1: jazz person is cooking person, who is romance -> jazz at pos_romance
            if music[pos_romance] != 'jazz':
                continue

            # Clue 7 and 10: rock person keeps horse and loves mystery -> same house as 'mystery'
            pos_rock = music.index('rock')
            if books[pos_rock] != 'mystery':
                continue

            # Clue 14: rock directly left of Jan -> rock cannot be last house
            if pos_rock == 3:
                continue

            # Hobbies permutations
            for hobbies in permutations(Hobbies):
                # Clue 11: painting directly left of romance
                if hobbies[pos_romance - 1] != 'painting':
                    continue
                # Clue 1: cooking same as romance
                if hobbies[pos_romance] != 'cooking':
                    continue

                # Birthdays determined by constraints
                # Clue 14: rock directly left of Jan
                pos_jan = pos_rock + 1
                # Clue 2: Feb same as pop (also Clue 12 Peter=pop handled later)
                pos_pop = music.index('pop')
                pos_feb = pos_pop
                # Clue 8 and 13: gardening same as April and gardener is Arnold -> April at pos_gardening
                pos_gardening = hobbies.index('gardening')
                pos_april = pos_gardening

                # Check distinct positions for Jan, Feb, April
                if len({pos_jan, pos_feb, pos_april}) != 3:
                    continue

                # Assign birthdays to houses
                birthday_at = [None] * 4
                birthday_at[pos_jan] = 'jan'
                birthday_at[pos_feb] = 'feb'
                birthday_at[pos_april] = 'april'
                # Remaining month is 'sept'
                remaining_house = [i for i in houses if birthday_at[i] is None]
                if len(remaining_house) != 1:
                    continue
                birthday_at[remaining_house[0]] = 'sept'

                # Animals permutations
                for animals in permutations(Animals):
                    # Clue 5: Feb is fish
                    if animals[pos_feb] != 'fish':
                        continue
                    # Clue 7: horse same as rock
                    if animals[pos_rock] != 'horse':
                        continue
                    # Clue 16: cat to the right of horse
                    if animals.index('cat') <= animals.index('horse'):
                        continue

                    # Names permutations
                    for names in permutations(Names):
                        # Clue 12: Peter is pop
                        if names[pos_pop] != 'Peter':
                            continue
                        # Clue 13: gardening is Arnold
                        if names[pos_gardening] != 'Arnold':
                            continue
                        # Clue 6: Alice is to the right of fantasy
                        if names.index('Alice') <= books.index('fantasy'):
                            continue
                        # Clue 3: Eric is not in the second house (index 1)
                        if names[1] == 'Eric':
                            continue

                        # All constraints satisfied, record solution
                        solution = {
                            "Name": names,
                            "Hobby": hobbies,
                            "Animal": animals,
                            "BookGenre": books,
                            "Birthday": birthday_at,
                            "MusicGenre": music
                        }
                        solutions.append(solution)

    # Use the first solution (should be unique)
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    header = ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"]
    rows = []
    for i in range(4):
        row = [
            str(i + 1),
            sol["Name"][i],
            sol["Hobby"][i],
            sol["Animal"][i],
            sol["BookGenre"][i],
            sol["Birthday"][i],
            sol["MusicGenre"][i],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))