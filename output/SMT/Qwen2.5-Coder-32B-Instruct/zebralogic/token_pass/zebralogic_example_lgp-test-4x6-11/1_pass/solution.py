from z3 import *

# Define variables
house = [Int(f"house_{i}") for i in range(1, 5)]
name = [Int(f"name_{i}") for i in range(1, 5)]
hobby = [Int(f"hobby_{i}") for i in range(1, 5)]
animal = [Int(f"animal_{i}") for i in range(1, 5)]
book_genre = [Int(f"book_genre_{i}") for i in range(1, 5)]
birthday = [Int(f"birthday_{i}") for i in range(1, 5)]
music_genre = [Int(f"music_genre_{i}") for i in range(1, 5)]

# Define domains
names = {"Peter": 1, "Alice": 2, "Eric": 3, "Arnold": 4}
hobbies = {"cooking": 1, "painting": 2, "gardening": 3, "photography": 4}
animals = {"horse": 1, "fish": 2, "cat": 3, "bird": 4}
book_genres = {"fantasy": 1, "mystery": 2, "romance": 3, "science fiction": 4}
birthdays = {"april": 1, "jan": 2, "sept": 3, "feb": 4}
music_genres = {"pop": 1, "rock": 2, "classical": 3, "jazz": 4}

# Create solver
solver = Solver()

# Add constraints for uniqueness
for lst in [name, hobby, animal, book_genre, birthday, music_genre]:
    solver.add(Distinct(lst))

# Clue 1
solver.add(hobby[book_genres["romance"] - 1] == hobbies["cooking"])

# Clue 2
solver.add(birthday[music_genres["pop"] - 1] == birthdays["feb"])

# Clue 3
solver.add(name[1] != names["Eric"])

# Clue 4
solver.add(book_genre[3] != book_genres["romance"])

# Clue 5
solver.add(birthday[animals["fish"] - 1] == birthdays["feb"])

# Clue 6
solver.add(name[hobby.index(hobbies["fantasy"]) + 1:] == [names["Alice"]])

# Clue 7
solver.add(animal[music_genres["rock"] - 1] == animals["horse"])

# Clue 8
solver.add(hobby[birthdays["april"] - 1] == hobbies["gardening"])

# Clue 9
solver.add(music_genres["jazz"] == hobbies["cooking"])

# Clue 10
solver.add(music_genres["rock"] == book_genres["mystery"])

# Clue 11
solver.add(hobby[hobby.index(hobbies["painting"]) + 1] == book_genres["romance"])

# Clue 12
solver.add(name[music_genres["pop"] - 1] == names["Peter"])

# Clue 13
solver.add(name[hobby.index(hobbies["gardening"]) + 1] == names["Arnold"])

# Clue 14
solver.add(birthday[music_genres["rock"] - 1] + 1 == birthday[music_genres["jazz"] - 1])

# Clue 15
solver.add(hobby[2] != hobbies["cooking"])

# Clue 16
solver.add(animal[animal.index(animals["horse"]) + 1:] == [animals["cat"]])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": []
        }
    }
    
    for h in range(1, 5):
        house_name = next(key for key, value in names.items() if model.evaluate(name[h-1]) == value)
        house_hobby = next(key for key, value in hobbies.items() if model.evaluate(hobby[h-1]) == value)
        house_animal = next(key for key, value in animals.items() if model.evaluate(animal[h-1]) == value)
        house_book_genre = next(key for key, value in book_genres.items() if model.evaluate(book_genre[h-1]) == value)
        house_birthday = next(key for key, value in birthdays.items() if model.evaluate(birthday[h-1]) == value)
        house_music_genre = next(key for key, value in music_genres.items() if model.evaluate(music_genre[h-1]) == value)
        
        solution["solution"]["rows"].append([
            str(h),
            house_name,
            house_hobby,
            house_animal,
            house_book_genre,
            house_birthday,
            house_music_genre
        ])
    
    print(solution)
else:
    print("No solution found")