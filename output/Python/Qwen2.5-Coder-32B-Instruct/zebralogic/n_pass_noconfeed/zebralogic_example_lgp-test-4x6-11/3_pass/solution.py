import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    book_genres = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    music_genres = ["pop", "rock", "classical", "jazz"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(4)))

    # Iterate over all possible combinations of permutations
    for name_order in all_permutations:
        for hobby_order in all_permutations:
            for animal_order in all_permutations:
                for book_genre_order in all_permutations:
                    for birthday_order in all_permutations:
                        for music_genre_order in all_permutations:
                            # Create a dictionary to store the current assignment
                            assignment = {
                                "name": {names[i]: i+1 for i in name_order},
                                "hobby": {hobbies[i]: i+1 for i in hobby_order},
                                "animal": {animals[i]: i+1 for i in animal_order},
                                "book_genre": {book_genres[i]: i+1 for i in book_genre_order},
                                "birthday": {birthdays[i]: i+1 for i in birthday_order},
                                "music_genre": {music_genres[i]: i+1 for i in music_genre_order}
                            }

                            # Check all the clues
                            if (
                                # Clue 1: The person who likes cooking reads romance books.
                                assignment["hobby"]["cooking"] == assignment["book_genre"]["romance"] and
                                # Clue 2: The person born in February listens to pop music.
                                assignment["birthday"]["feb"] == assignment["music_genre"]["pop"] and
                                # Clue 3: Eric does not live in the second house.
                                assignment["name"]["Eric"] != 2 and
                                # Clue 4: The person who reads romance books does not live in the fourth house.
                                assignment["book_genre"]["romance"] != 4 and
                                # Clue 5: The person born in February has a fish.
                                assignment["birthday"]["feb"] == assignment["animal"]["fish"] and
                                # Clue 6: Alice lives in a house with a number higher than the house where the person who reads fantasy books lives.
                                assignment["name"]["Alice"] > assignment["book_genre"]["fantasy"] and
                                # Clue 7: The person who has a horse listens to rock music.
                                assignment["animal"]["horse"] == assignment["music_genre"]["rock"] and
                                # Clue 8: The person who gardens was born in April.
                                assignment["hobby"]["gardening"] == assignment["birthday"]["april"] and
                                # Clue 9: The person who listens to jazz likes cooking.
                                assignment["music_genre"]["jazz"] == assignment["hobby"]["cooking"] and
                                # Clue 10: The person who listens to rock music reads mystery books.
                                assignment["music_genre"]["rock"] == assignment["book_genre"]["mystery"] and
                                # Clue 11: The person who paints lives in a house with a number one higher than the house where the person who reads romance books lives.
                                assignment["hobby"]["painting"] + 1 == assignment["book_genre"]["romance"] and
                                # Clue 12: Peter listens to pop music.
                                assignment["name"]["Peter"] == assignment["music_genre"]["pop"] and
                                # Clue 13: Arnold gardens.
                                assignment["name"]["Arnold"] == assignment["hobby"]["gardening"] and
                                # Clue 14: The person who listens to rock music was born in January.
                                assignment["music_genre"]["rock"] + 1 == assignment["birthday"]["jan"] and
                                # Clue 15: The person who likes cooking does not live in the third house.
                                assignment["hobby"]["cooking"] != 3 and
                                # Clue 16: The cat lives in a house with a number higher than the house where the horse lives.
                                assignment["animal"]["cat"] > assignment["animal"]["horse"]
                            ):
                                # If all clues are satisfied, construct the solution
                                solution = []
                                for house in range(1, 5):
                                    name = next(k for k, v in assignment["name"].items() if v == house)
                                    hobby = next(k for k, v in assignment["hobby"].items() if v == house)
                                    animal = next(k for k, v in assignment["animal"].items() if v == house)
                                    book_genre = next(k for k, v in assignment["book_genre"].items() if v == house)
                                    birthday = next(k for k, v in assignment["birthday"].items() if v == house)
                                    music_genre = next(k for k, v in assignment["music_genre"].items() if v == house)
                                    solution.append([str(house), name, hobby, animal, book_genre, birthday, music_genre])

                                # Output the solution as JSON
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                        "rows": solution
                                    }
                                }
                                print(json.dumps(result))
                                return

# Run the solver
solve_puzzle()