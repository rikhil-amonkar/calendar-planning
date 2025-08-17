import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']

    for name_p in itertools.permutations(names):
        if name_p[0] != 'Eric':
            continue  # Clue 7
        for smoothie_p in itertools.permutations(smoothies):
            if smoothie_p[0] != 'watermelon':
                continue  # Clue 9
            for book_p in itertools.permutations(book_genres):
                for birth_p in itertools.permutations(birthdays):
                    for height_p in itertools.permutations(heights):
                        # Clue 8: Watermelon lover is short
                        if height_p[0] != 'short':
                            continue
                        # Clue 1: Cherry not in house 2
                        if any(smoothie_p[i] == 'cherry' and (i + 1) == 2 for i in range(3)):
                            continue
                        # Clue 2: Arnold's book is mystery
                        arnold_index = None
                        for i in range(3):
                            if name_p[i] == 'Arnold':
                                arnold_index = i
                                break
                        if book_p[arnold_index] != 'mystery':
                            continue
                        # Clue 3: Jan not in first house
                        if birth_p[0] == 'jan':
                            continue
                        # Clue 4: very short iff romance
                        valid_clue4 = True
                        for i in range(3):
                            if (book_p[i] == 'romance') != (height_p[i] == 'very short'):
                                valid_clue4 = False
                                break
                        if not valid_clue4:
                            continue
                        # Clue 5: Mystery book has Sept birthday
                        mystery_index = None
                        for i in range(3):
                            if book_p[i] == 'mystery':
                                mystery_index = i
                                break
                        if birth_p[mystery_index] != 'sept':
                            continue
                        # Clue 6: average height iff desert smoothie
                        valid_clue6 = True
                        for i in range(3):
                            avg = (height_p[i] == 'average')
                            desert = (smoothie_p[i] == 'desert')
                            if avg != desert:
                                valid_clue6 = False
                                break
                        if not valid_clue6:
                            continue
                        # All constraints passed
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                "rows": []
                            }
                        }
                        for i in range(3):
                            house_num = str(i + 1)
                            row = [
                                house_num,
                                name_p[i],
                                book_p[i],
                                smoothie_p[i],
                                birth_p[i],
                                height_p[i]
                            ]
                            solution['solution']['rows'].append(row)
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()