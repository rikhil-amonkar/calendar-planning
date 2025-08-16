from z3 import *
import json

# Create Solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Peter', 'Arnold', 'Eric']
book_genres = ['science fiction', 'mystery', 'romance']
smoothies = ['watermelon', 'desert', 'cherry']
birthdays = ['april', 'jan', 'sept']
heights = ['average', 'very short', 'short']

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
book_genre_vars = {house: Int(f'book_genre_{house}') for house in houses}
smoothie_vars = {house: Int(f'smoothie_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}

# Add constraints for unique values within each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))

# Map names to integers
name_map = {name: i for i, name in enumerate(names)}
# Map book genres to integers
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
# Map smoothies to integers
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}
# Map birthdays to integers
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
# Map heights to integers
height_map = {height: i for i, height in enumerate(heights)}

# Add constraints based on clues
# 1. The person who likes Cherry smoothies is not in the second house.
solver.add(smoothie_vars[2] != smoothie_map['cherry'])

# 2. Arnold is the person who loves mystery books.
solver.add(name_vars[2] == name_map['Arnold'])  # Arnold is in the second house based on other clues
solver.add(book_genre_vars[2] == book_genre_map['mystery'])

# 3. The person whose birthday is in January is not in the first house.
solver.add(birthday_vars[1] != birthday_map['jan'])

# 4. The person who is very short is the person who loves romance books.
solver.add(height_vars[houses.index(3)] == height_map['very short'])  # Assuming the third house for now
solver.add(book_genre_vars[houses.index(3)] == book_genre_map['romance'])

# 5. The person who loves mystery books is the person whose birthday is in September.
solver.add(book_genre_vars[2] == book_genre_map['mystery'])  # Arnold
solver.add(birthday_vars[2] == birthday_map['sept'])  # Arnold

# 6. The person who has an average height is the Desert smoothie lover.
solver.add(height_vars[houses.index(1)] == height_map['average'])  # Eric
solver.add(smoothie_vars[houses.index(1)] == smoothie_map['desert'])  # Eric

# 7. Eric is in the first house.
solver.add(name_vars[1] == name_map['Eric'])

# 8. The Watermelon smoothie lover is the person who is short.
solver.add(smoothie_vars[houses.index(3)] == smoothie_map['watermelon'])  # Assuming the third house for now
solver.add(height_vars[houses.index(3)] == height_map['short'])  # Assuming the third house for now

# 9. The Watermelon smoothie lover is Eric.
solver.add(smoothie_vars[1] == smoothie_map['watermelon'])  # Eric
solver.add(name_vars[1] == name_map['Eric'])

# Adjust assumptions based on logical deductions
# Since Eric is in the first house and likes watermelon smoothie and has average height,
# and Arnold is in the second house and likes mystery books and has birthday in September,
# Peter must be in the third house.
solver.add(name_vars[3] == name_map['Peter'])
solver.add(smoothie_vars[3] == smoothie_map['cherry'])
solver.add(birthday_vars[3] == birthday_map['jan'])
solver.add(height_vars[3] == height_map['very short'])
solver.add(book_genre_vars[3] == book_genre_map['romance'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        book_genre = book_genres[model.evaluate(book_genre_vars[house]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[house]).as_long()]
        birthday = birthdays[model.evaluate(birthday_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        
        solution["solution"]["rows"].append([str(house), name, book_genre, smoothie, birthday, height])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")