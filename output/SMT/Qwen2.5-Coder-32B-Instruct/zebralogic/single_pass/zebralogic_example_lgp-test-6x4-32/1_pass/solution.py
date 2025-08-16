from z3 import *

# Define the variables
names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
house_styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
music_genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

# Create Z3 variables
house_vars = [Int(f'house_{i+1}') for i in range(6)]
name_vars = {name: Int(f'name_{name}') for name in names}
house_style_vars = {style: Int(f'house_style_{style}') for style in house_styles}
music_genre_vars = {genre: Int(f'music_genre_{genre}') for genre in music_genres}
hobby_vars = {hobby: Int(f'hobby_{hobby}') for hobby in hobbies}

# Create the solver
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct(house_vars))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(house_style_vars.values()))
solver.add(Distinct(music_genre_vars.values()))
solver.add(Distinct(hobby_vars.values()))

# Map names to house numbers
for name in names:
    solver.add(name_vars[name] >= 1)
    solver.add(name_vars[name] <= 6)

# Map house styles to house numbers
for style in house_styles:
    solver.add(house_style_vars[style] >= 1)
    solver.add(house_style_vars[style] <= 6)

# Map music genres to house numbers
for genre in music_genres:
    solver.add(music_genre_vars[genre] >= 1)
    solver.add(music_genre_vars[genre] <= 6)

# Map hobbies to house numbers
for hobby in hobbies:
    solver.add(hobby_vars[hobby] >= 1)
    solver.add(hobby_vars[hobby] <= 6)

# Add clues as constraints
# 1. The person who loves rock music is in the fifth house.
solver.add(music_genre_vars['rock'] == 5)

# 2. The person who loves classical music and the woodworking hobbyist are next to each other.
solver.add(Or(
    And(music_genre_vars['classical'] + 1 == hobby_vars['woodworking']),
    And(music_genre_vars['classical'] - 1 == hobby_vars['woodworking'])
))

# 3. The person in a Mediterranean-style villa is the person who loves hip-hop music.
solver.add(And(house_style_vars['mediterranean'] == music_genre_vars['hip hop']))

# 4. There are two houses between Arnold and the person residing in a Victorian house.
solver.add(Or(
    And(name_vars['Arnold'] + 3 == house_style_vars['victorian']),
    And(name_vars['Arnold'] - 3 == house_style_vars['victorian'])
))

# 5. The person who loves jazz music is directly left of Eric.
solver.add(music_genre_vars['jazz'] + 1 == name_vars['Eric'])

# 6. The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
solver.add(music_genre_vars['hip hop'] < hobby_vars['knitting'])

# 7. Carol is the person who loves hip-hop music.
solver.add(name_vars['Carol'] == music_genre_vars['hip hop'])

# 8. The person in a Craftsman-style house is Arnold.
solver.add(house_style_vars['craftsman'] == name_vars['Arnold'])

# 9. The person in a ranch-style home is Eric.
solver.add(house_style_vars['ranch'] == name_vars['Eric'])

# 10. The woodworking hobbyist is the person residing in a Victorian house.
solver.add(hobby_vars['woodworking'] == house_style_vars['victorian'])

# 11. The person who loves country music is in the first house.
solver.add(music_genre_vars['country'] == 1)

# 12. There is one house between the person who paints as a hobby and the person living in a colonial-style house.
solver.add(Or(
    And(hobby_vars['painting'] + 2 == house_style_vars['colonial']),
    And(hobby_vars['painting'] - 2 == house_style_vars['colonial'])
))

# 13. Alice is the photography enthusiast.
solver.add(name_vars['Alice'] == hobby_vars['photography'])

# 14. The person who enjoys gardening is Eric.
solver.add(hobby_vars['gardening'] == name_vars['Eric'])

# 15. Bob is in the third house.
solver.add(name_vars['Bob'] == 3)

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": []
        }
    }
    
    # Create a mapping from house number to attributes
    house_to_attributes = {}
    for house in range(1, 7):
        house_to_attributes[house] = {
            "Name": None,
            "HouseStyle": None,
            "MusicGenre": None,
            "Hobby": None
        }
    
    for name, var in name_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[house_number]["Name"] = name
    
    for style, var in house_style_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[house_number]["HouseStyle"] = style
    
    for genre, var in music_genre_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[house_number]["MusicGenre"] = genre
    
    for hobby, var in hobby_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[house_number]["Hobby"] = hobby
    
    # Populate the rows
    for house in range(1, 7):
        attributes = house_to_attributes[house]
        solution["solution"]["rows"].append([
            str(house),
            attributes["Name"],
            attributes["HouseStyle"],
            attributes["MusicGenre"],
            attributes["Hobby"]
        ])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")