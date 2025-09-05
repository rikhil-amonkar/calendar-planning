from z3 import Int, Solver, And, Distinct, sat
import json

# Create solver
s = Solver()

# Define variables for each category
# Names
Peter = Int('Peter')
Alice = Int('Alice')
Eric = Int('Eric')
Arnold = Int('Arnold')

# Hobbies
cooking = Int('cooking')
painting = Int('painting')
gardening = Int('gardening')
photography = Int('photography')

# Animals
horse = Int('horse')
fish = Int('fish')
cat = Int('cat')
bird = Int('bird')

# Book Genres
fantasy = Int('fantasy')
mystery = Int('mystery')
romance = Int('romance')
science_fiction = Int('science_fiction')

# Birthdays
april = Int('april')
jan = Int('jan')
sept = Int('sept')
feb = Int('feb')

# Music Genres
pop = Int('pop')
rock = Int('rock')
classical = Int('classical')
jazz = Int('jazz')

# All variables must be between 1 and 4 (houses 1 through 4)
all_vars = [Peter, Alice, Eric, Arnold,
            cooking, painting, gardening, photography,
            horse, fish, cat, bird,
            fantasy, mystery, romance, science_fiction,
            april, jan, sept, feb,
            pop, rock, classical, jazz]

for var in all_vars:
    s.add(var >= 1, var <= 4)

# All different constraints within each category
s.add(Distinct(Peter, Alice, Eric, Arnold))
s.add(Distinct(cooking, painting, gardening, photography))
s.add(Distinct(horse, fish, cat, bird))
s.add(Distinct(fantasy, mystery, romance, science_fiction))
s.add(Distinct(april, jan, sept, feb))
s.add(Distinct(pop, rock, classical, jazz))

# Puzzle constraints
# 1. The person who loves cooking is the person who loves romance books.
s.add(cooking == romance)

# 2. The person whose birthday is in February is the person who loves pop music.
s.add(feb == pop)

# 3. Eric is not in the second house.
s.add(Eric != 2)

# 4. The person who loves romance books is not in the fourth house.
s.add(romance != 4)

# 5. The person whose birthday is in February is the fish enthusiast.
s.add(feb == fish)

# 6. Alice is somewhere to the right of the person who loves fantasy books.
s.add(Alice > fantasy)

# 7. The person who keeps horses is the person who loves rock music.
s.add(horse == rock)

# 8. The person who enjoys gardening is the person whose birthday is in April.
s.add(gardening == april)

# 9. The person who loves jazz music is the person who loves cooking.
s.add(jazz == cooking)

# 10. The person who loves rock music is the person who loves mystery books.
s.add(rock == mystery)

# 11. The person who paints as a hobby is directly left of the person who loves romance books.
s.add(painting + 1 == romance)

# 12. Peter is the person who loves pop music.
s.add(pop == Peter)

# 13. The person who enjoys gardening is Arnold.
s.add(gardening == Arnold)

# 14. The person who loves rock music is directly left of the person whose birthday is in January.
s.add(rock + 1 == jan)

# 15. The person who loves cooking is not in the third house.
s.add(cooking != 3)

# 16. The cat lover is somewhere to the right of the person who keeps horses.
s.add(cat > horse)

# Check satisfiability
if s.check() == sat:
    m = s.model()
    
    # Build reverse lookup dictionaries for each category
    names = {
        "Peter": m[Peter].as_long(),
        "Alice": m[Alice].as_long(),
        "Eric": m[Eric].as_long(),
        "Arnold": m[Arnold].as_long()
    }
    
    hobbies = {
        "cooking": m[cooking].as_long(),
        "painting": m[painting].as_long(),
        "gardening": m[gardening].as_long(),
        "photography": m[photography].as_long()
    }
    
    animals = {
        "horse": m[horse].as_long(),
        "fish": m[fish].as_long(),
        "cat": m[cat].as_long(),
        "bird": m[bird].as_long()
    }
    
    book_genres = {
        "fantasy": m[fantasy].as_long(),
        "mystery": m[mystery].as_long(),
        "romance": m[romance].as_long(),
        "science fiction": m[science_fiction].as_long()
    }
    
    birthdays = {
        "april": m[april].as_long(),
        "jan": m[jan].as_long(),
        "sept": m[sept].as_long(),
        "feb": m[feb].as_long()
    }
    
    music_genres = {
        "pop": m[pop].as_long(),
        "rock": m[rock].as_long(),
        "classical": m[classical].as_long(),
        "jazz": m[jazz].as_long()
    }
    
    # Function to get attribute by house number from a mapping
    def get_by_house(mapping, house_num):
        for key, value in mapping.items():
            if value == house_num:
                return key
        return None

    # Construct rows for houses 1 through 4 in order
    rows = []
    for house in range(1, 5):
        row = [
            str(house),
            get_by_house(names, house),
            get_by_house(hobbies, house),
            get_by_house(animals, house),
            get_by_house(book_genres, house),
            get_by_house(birthdays, house),
            get_by_house(music_genres, house)
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"solution": "no solution found"}))