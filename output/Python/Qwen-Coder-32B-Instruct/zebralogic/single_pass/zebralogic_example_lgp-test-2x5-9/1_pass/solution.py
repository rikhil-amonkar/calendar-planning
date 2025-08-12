import json
from itertools import permutations

# Define the attributes
names = ["Arnold", "Eric"]
book_genres = ["science fiction", "mystery"]
vacations = ["mountain", "beach"]
animals = ["cat", "horse"]
music_genres = ["rock", "pop"]

# Define the clues as functions
def clue1(people):
    return people[1]["vacation"] == "beach"

def clue2(people):
    return people[1]["music"] == "pop"

def clue3(people):
    return people[0]["music"] == "rock" and people[0]["book_genre"] == "mystery"

def clue4(people):
    return people[0]["animal"] == "cat"

def clue5(people):
    return people[0]["book_genre"] == "mystery"

# Generate all possible permutations
all_permutations = permutations(zip(names, book_genres, vacations, animals, music_genres))

# Check each permutation against the clues
for perm in all_permutations:
    people = [{"name": p[0], "book_genre": p[1], "vacation": p[2], "animal": p[3], "music": p[4]} for p in perm]
    if clue1(people) and clue2(people) and clue3(people) and clue4(people) and clue5(people):
        solution = {
            "solution": {
                "header": ["House", "Name", "Favorite Book Genre", "Vacation Preference", "Animal", "Favorite Music Genre"],
                "rows": [
                    ["1", people[0]["name"], people[0]["book_genre"], people[0]["vacation"], people[0]["animal"], people[0]["music"]],
                    ["2", people[1]["name"], people[1]["book_genre"], people[1]["vacation"], people[1]["animal"], people[1]["music"]]
                ]
            }
        }
        break

print(json.dumps(solution))