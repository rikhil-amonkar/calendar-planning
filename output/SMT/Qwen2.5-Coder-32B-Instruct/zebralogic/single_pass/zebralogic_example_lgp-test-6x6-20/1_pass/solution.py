from z3 import *

# Create variables
names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

houses = range(1, 7)

# Create Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
music_genre_vars = {house: Int(f'music_genre_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
food_vars = {house: Int(f'food_{house}') for house in houses}

# Create solvers
solver = Solver()

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(cigar_vars[house] >= 0)
    solver.add(cigar_vars[house] < len(cigars))
    solver.add(music_genre_vars[house] >= 0)
    solver.add(music_genre_vars[house] < len(music_genres))
    solver.add(drink_vars[house] >= 0)
    solver.add(drink_vars[house] < len(drinks))
    solver.add(mother_vars[house] >= 0)
    solver.add(mother_vars[house] < len(mothers))
    solver.add(food_vars[house] >= 0)
    solver.add(food_vars[house] < len(foods))

# Add uniqueness constraints
for var_dict in [name_vars, cigar_vars, music_genre_vars, drink_vars, mother_vars, food_vars]:
    solver.add(Distinct([var_dict[house] for house in houses]))

# Add clues
# 1. Carol is directly left of the person who loves eating grilled cheese.
solver.add(Or([And(name_vars[i] == names.index('Carol'), food_vars[i + 1] == foods.index('grilled cheese')) for i in range(1, 6)]))

# 2. Eric is not in the second house.
solver.add(name_vars[2] != names.index('Eric'))

# 3. The person whose mother's name is Holly is somewhere to the right of Carol.
solver.add(Or([And(mother_vars[i] == mothers.index('Holly'), name_vars[j] == names.index('Carol')) for i in range(2, 7) for j in range(1, i)]))

# 4. The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
solver.add(Or([And(food_vars[i] == foods.index('grilled cheese'), music_genre_vars[j] == music_genres.index('rock')) for i in range(2, 7) for j in range(1, i)]))

# 5. Eric is directly left of Carol.
solver.add(Or([And(name_vars[i] == names.index('Eric'), name_vars[i + 1] == names.index('Carol')) for i in range(1, 6)]))

# 6. The person who loves pop music is not in the third house.
solver.add(music_genre_vars[3] != music_genres.index('pop'))

# 7. Eric is the person who loves country music.
solver.add(And(name_vars[i] == names.index('Eric'), music_genre_vars[i] == music_genres.index('country')) for i in houses)

# 8. The person who loves classical music is in the sixth house.
solver.add(music_genre_vars[6] == music_genres.index('classical'))

# 9. The coffee drinker is Bob.
solver.add(And(drink_vars[i] == drinks.index('coffee'), name_vars[i] == names.index('Bob')) for i in houses)

# 10. The person who smokes many unique blends is Peter.
solver.add(And(cigar_vars[i] == cigars.index('blends'), name_vars[i] == names.index('Peter')) for i in houses)

# 11. The person who loves the stew is not in the fifth house.
solver.add(food_vars[5] != foods.index('stew'))

# 12. The root beer lover is directly left of The person whose mother's name is Janelle.
solver.add(Or([And(drink_vars[i] == drinks.index('root beer'), mother_vars[i + 1] == mothers.index('Janelle')) for i in range(1, 6)]))

# 13. There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
solver.add(Or([And(mother_vars[i] == mothers.index('Sarah'), cigar_vars[i + 3] == cigars.index('yellow monster')) for i in range(1, 4)] +
              [And(mother_vars[i] == mothers.index('Sarah'), cigar_vars[i - 3] == cigars.index('yellow monster')) for i in range(4, 7)]))

# 14. Eric is the tea drinker.
solver.add(And(name_vars[i] == names.index('Eric'), drink_vars[i] == drinks.index('tea')) for i in houses)

# 15. The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
solver.add(Or([And(cigar_vars[i] == cigars.index('pall mall'), food_vars[j] == foods.index('stir fry')) for i in range(2, 7) for j in range(1, i)]))

# 16. The person who loves the soup is Bob.
solver.add(And(food_vars[i] == foods.index('soup'), name_vars[i] == names.index('Bob')) for i in houses)

# 17. The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
solver.add(Or([And(music_genre_vars[i] == music_genres.index('hip hop'), mother_vars[i + 1] == mothers.index('Kailyn')) for i in range(1, 6)]))

# 18. Arnold is somewhere to the right of The person whose mother's name is Kailyn.
solver.add(Or([And(name_vars[i] == names.index('Arnold'), mother_vars[j] == mothers.index('Kailyn')) for i in range(2, 7) for j in range(1, i)]))

# 19. The one who only drinks water is directly left of the person who smokes Blue Master.
solver.add(Or([And(drink_vars[i] == drinks.index('water'), cigar_vars[i + 1] == cigars.index('blue master')) for i in range(1, 6)]))

# 20. The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
solver.add(Or([And(food_vars[i] == foods.index('spaghetti'), cigar_vars[j] == cigars.index('blends')) for i in range(1, 6) for j in range(i + 1, 7)]))

# 21. The person whose mother's name is Sarah is directly left of the person who loves jazz music.
solver.add(Or([And(mother_vars[i] == mothers.index('Sarah'), music_genre_vars[i + 1] == music_genres.index('jazz')) for i in range(1, 6)]))

# 22. The person who loves hip-hop music is directly left of the root beer lover.
solver.add(Or([And(music_genre_vars[i] == music_genres.index('hip hop'), drink_vars[i + 1] == drinks.index('root beer')) for i in range(1, 6)]))

# 23. The one who only drinks water is the person who loves the stew.
solver.add(And(drink_vars[i] == drinks.index('water'), food_vars[i] == foods.index('stew')) for i in houses)

# 24. The Dunhill smoker is not in the second house.
solver.add(cigar_vars[2] != cigars.index('dunhill'))

# 25. The person who likes milk is The person whose mother's name is Janelle.
solver.add(And(drink_vars[i] == drinks.index('milk'), mother_vars[i] == mothers.index('Janelle')) for i in houses)

# 26. Eric is The person whose mother's name is Aniya.
solver.add(And(name_vars[i] == names.index('Eric'), mother_vars[i] == mothers.index('Aniya')) for i in houses)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        cigar = cigars[model.evaluate(cigar_vars[house]).as_long()]
        music_genre = music_genres[model.evaluate(music_genre_vars[house]).as_long()]
        drink = drinks[model.evaluate(drink_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        food = foods[model.evaluate(food_vars[house]).as_long()]
        solution.append([str(house), name, cigar, music_genre, drink, mother, food])
    
    print({
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": solution
        }
    })
else:
    print("No solution found")