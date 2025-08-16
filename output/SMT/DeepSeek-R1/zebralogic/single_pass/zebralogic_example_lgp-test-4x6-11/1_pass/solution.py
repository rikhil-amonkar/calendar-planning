from z3 import *

def main():
    # Define the attributes and their possible values
    Name, (Name_Peter, Name_Alice, Name_Eric, Name_Arnold) = EnumSort('Name', ['Peter', 'Alice', 'Eric', 'Arnold'])
    Hobby, (Hobby_cooking, Hobby_painting, Hobby_gardening, Hobby_photography) = EnumSort('Hobby', ['cooking', 'painting', 'gardening', 'photography'])
    Animal, (Animal_horse, Animal_fish, Animal_cat, Animal_bird) = EnumSort('Animal', ['horse', 'fish', 'cat', 'bird'])
    BookGenre, (BookGenre_fantasy, BookGenre_mystery, BookGenre_romance, BookGenre_science_fiction) = EnumSort('BookGenre', ['fantasy', 'mystery', 'romance', 'science fiction'])
    Birthday, (Birthday_april, Birthday_jan, Birthday_sept, Birthday_feb) = EnumSort('Birthday', ['april', 'jan', 'sept', 'feb'])
    MusicGenre, (MusicGenre_pop, MusicGenre_rock, MusicGenre_classical, MusicGenre_jazz) = EnumSort('MusicGenre', ['pop', 'rock', 'classical', 'jazz'])

    # Create arrays for each attribute for the 4 houses (index 0 to 3 for house1 to house4)
    names = [Const(f'name_{i}', Name) for i in range(4)]
    hobbies = [Const(f'hobby_{i}', Hobby) for i in range(4)]
    animals = [Const(f'animal_{i}', Animal) for i in range(4)]
    books = [Const(f'book_{i}', BookGenre) for i in range(4)]
    birthdays = [Const(f'birthday_{i}', Birthday) for i in range(4)]
    musics = [Const(f'music_{i}', MusicGenre) for i in range(4)]

    s = Solver()

    # Add distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(hobbies))
    s.add(Distinct(animals))
    s.add(Distinct(books))
    s.add(Distinct(birthdays))
    s.add(Distinct(musics))

    # Clue 1: The person who loves cooking is the person who loves romance books.
    for i in range(4):
        s.add( (hobbies[i] == Hobby_cooking) == (books[i] == BookGenre_romance) )

    # Clue 2: The person whose birthday is in February is the person who loves pop music.
    for i in range(4):
        s.add( (birthdays[i] == Birthday_feb) == (musics[i] == MusicGenre_pop) )

    # Clue 3: Eric is not in the second house.
    s.add(names[1] != Name_Eric)  # house2 is index1

    # Clue 4: The person who loves romance books is not in the fourth house.
    s.add(books[3] != BookGenre_romance)

    # Clue 5: The person whose birthday is in February is the fish enthusiast.
    for i in range(4):
        s.add( (birthdays[i] == Birthday_feb) == (animals[i] == Animal_fish) )

    # Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
    # There exists a house i (fantasy) and a house j (Alice) such that j > i.
    s.add(Or([And(books[i] == BookGenre_fantasy, names[j] == Name_Alice, j > i) for i in range(4) for j in range(4)]))

    # Clue 7: The person who keeps horses is the person who loves rock music.
    for i in range(4):
        s.add( (animals[i] == Animal_horse) == (musics[i] == MusicGenre_rock) )

    # Clue 8: The person who enjoys gardening is the person whose birthday is in April.
    for i in range(4):
        s.add( (hobbies[i] == Hobby_gardening) == (birthdays[i] == Birthday_april) )

    # Clue 9: The person who loves jazz music is the person who loves cooking.
    for i in range(4):
        s.add( (musics[i] == MusicGenre_jazz) == (hobbies[i] == Hobby_cooking) )

    # Clue 10: The person who loves rock music is the person who loves mystery books.
    for i in range(4):
        s.add( (musics[i] == MusicGenre_rock) == (books[i] == BookGenre_mystery) )

    # Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
    s.add(Or([And(hobbies[i] == Hobby_painting, books[i+1] == BookGenre_romance) for i in range(3)]))

    # Clue 12: Peter is the person who loves pop music.
    for i in range(4):
        s.add( (names[i] == Name_Peter) == (musics[i] == MusicGenre_pop) )

    # Clue 13: The person who enjoys gardening is Arnold.
    for i in range(4):
        s.add( (hobbies[i] == Hobby_gardening) == (names[i] == Name_Arnold) )

    # Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
    s.add(Or([And(musics[i] == MusicGenre_rock, birthdays[i+1] == Birthday_jan) for i in range(3)]))

    # Clue 15: The person who loves cooking is not in the third house.
    s.add(hobbies[2] != Hobby_cooking)

    # Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
    s.add(Or([And(animals[i] == Animal_horse, animals[j] == Animal_cat, j > i) for i in range(4) for j in range(4)]))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Mapping from Z3 constants to string values
        name_map = {
            Name_Peter: "Peter",
            Name_Alice: "Alice",
            Name_Eric: "Eric",
            Name_Arnold: "Arnold"
        }
        hobby_map = {
            Hobby_cooking: "cooking",
            Hobby_painting: "painting",
            Hobby_gardening: "gardening",
            Hobby_photography: "photography"
        }
        animal_map = {
            Animal_horse: "horse",
            Animal_fish: "fish",
            Animal_cat: "cat",
            Animal_bird: "bird"
        }
        book_map = {
            BookGenre_fantasy: "fantasy",
            BookGenre_mystery: "mystery",
            BookGenre_romance: "romance",
            BookGenre_science_fiction: "science fiction"
        }
        birthday_map = {
            Birthday_april: "april",
            Birthday_jan: "jan",
            Birthday_sept: "sept",
            Birthday_feb: "feb"
        }
        music_map = {
            MusicGenre_pop: "pop",
            MusicGenre_rock: "rock",
            MusicGenre_classical: "classical",
            MusicGenre_jazz: "jazz"
        }
        
        # Prepare the rows
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = name_map[m.evaluate(names[i])]
            hobby_val = hobby_map[m.evaluate(hobbies[i])]
            animal_val = animal_map[m.evaluate(animals[i])]
            book_val = book_map[m.evaluate(books[i])]
            birthday_val = birthday_map[m.evaluate(birthdays[i])]
            music_val = music_map[m.evaluate(musics[i])]
            rows.append([house_num, name_val, hobby_val, animal_val, book_val, birthday_val, music_val])
        
        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": rows
            }
        }
        
        # Output as JSON string (but the problem expects the Python dictionary for the final output, but we are to write a program that outputs the JSON)
        # However, the problem says: "Your output should be a JSON-formatted dictionary", but in the context, we are writing a Python program that prints the JSON.
        # But the instruction says: "Write a Python program that solves it using the Z3 solver. Always surround your final code with