from z3 import *

# Define the domains
houses = [1, 2, 3]
names = ["Peter", "Arnold", "Eric"]
book_genres = ["science fiction", "mystery", "romance"]
smoothies = ["watermelon", "desert", "cherry"]
birthdays = ["april", "jan", "sept"]
heights = ["average", "very short", "short"]

# Create variables
name_vars = {house: Int(f"name_{house}") for house in houses}
book_genre_vars = {house: Int(f"book_genre_{house}") for house in houses}
smoothie_vars = {house: Int(f"smoothie_{house}") for house in houses}
birthday_vars = {house: Int(f"birthday_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}

# Create solver
solver = Solver()

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(book_genre_vars[house] >= 0)
    solver.add(book_genre_vars[house] < len(book_genres))
    solver.add(smoothie_vars[house] >= 0)
    solver.add(smoothie_vars[house] < len(smoothies))
    solver.add(birthday_vars[house] >= 0)
    solver.add(birthday_vars[house] < len(birthdays))
    solver.add(height_vars[house] >= 0)
    solver.add(height_vars[house] < len(heights))

# Add uniqueness constraints
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(book_genre_vars.values())))
solver.add(Distinct(list(smoothie_vars.values())))
solver.add(Distinct(list(birthday_vars.values())))
solver.add(Distinct(list(height_vars.values())))

# Add clue constraints
# 1. The person who likes Cherry smoothies is not in the second house.
solver.add(smoothie_vars[2] != smoothies.index("cherry"))

# 2. Arnold is the person who loves mystery books.
for house in houses:
    solver.add(Or(name_vars[house] != names.index("Arnold"), book_genre_vars[house] != book_genres.index("mystery")))

# 3. The person whose birthday is in January is not in the first house.
solver.add(birthday_vars[1] != birthdays.index("jan"))

# 4. The person who is very short is the person who loves romance books.
for house in houses:
    solver.add(Or(height_vars[house] != heights.index("very short"), book_genre_vars[house] != book_genres.index("romance")))

# 5. The person who loves mystery books is the person whose birthday is in September.
for house in houses:
    solver.add(Or(book_genre_vars[house] != book_genres.index("mystery"), birthday_vars[house] != birthdays.index("sept")))

# 6. The person who has an average height is the Desert smoothie lover.
for house in houses:
    solver.add(Or(height_vars[house] != heights.index("average"), smoothie_vars[house] != smoothies.index("desert")))

# 7. Eric is in the first house.
solver.add(name_vars[1] == names.index("Eric"))

# 8. The Watermelon smoothie lover is the person who is short.
for house in houses:
    solver.add(Or(smoothie_vars[house] != smoothies.index("watermelon"), height_vars[house] != heights.index("short")))

# 9. The Watermelon smoothie lover is Eric.
for house in houses:
    solver.add(Or(smoothie_vars[house] != smoothies.index("watermelon"), name_vars[house] != names.index("Eric")))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        book_genre = book_genres[model[book_genre_vars[house]].as_long()]
        smoothie = smoothies[model[smoothie_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, book_genre, smoothie, birthday, height])
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")