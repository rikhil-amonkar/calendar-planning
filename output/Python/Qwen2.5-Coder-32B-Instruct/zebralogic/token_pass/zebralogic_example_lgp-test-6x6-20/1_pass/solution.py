import itertools
import json

# Define the constraints
constraints = [
    lambda data: data.index('Carol') + 1 == data.index('grilled cheese'),  # Carol is directly left of the person who loves eating grilled cheese.
    lambda data: data.index('Eric') != 1,  # Eric is not in the second house.
    lambda data: data.index('Holly') > data.index('Carol'),  # The person whose mother's name is Holly is somewhere to the right of Carol.
    lambda data: data.index('grilled cheese') > data.index('rock'),  # The person who loves eating grilled cheese is somewhere to the right of the person who loves rock music.
    lambda data: data.index('Eric') + 1 == data.index('Carol'),  # Eric is directly left of Carol.
    lambda data: data.index('pop') != 2,  # The person who loves pop music is not in the third house.
    lambda data: data[data.index('Eric')][3] == 'country',  # Eric is the person who loves country music.
    lambda data: data[5][3] == 'classical',  # The person who loves classical music is in the sixth house.
    lambda data: data[data.index('Bob')][4] == 'coffee',  # The coffee drinker is Bob.
    lambda data: data[data.index('Peter')][2] == 'blends',  # The person who smokes many unique blends is Peter.
    lambda data: data.index('stew') != 4,  # The person who loves the stew is not in the fifth house.
    lambda data: data.index('root beer') + 1 == data.index('Janelle'),  # The root beer lover is directly left of The person whose mother's name is Janelle.
    lambda data: abs(data.index('Sarah') - data.index('yellow monster')) == 3,  # There are two houses between The person whose mother's name is Sarah and the person who smokes Yellow Monster.
    lambda data: data[data.index('Eric')][4] == 'tea',  # Eric is the tea drinker.
    lambda data: data.index('pall mall') > data.index('stir fry'),  # The person partial to Pall Mall is somewhere to the right of the person who loves stir fry.
    lambda data: data[data.index('Bob')][5] == 'soup',  # The person who loves the soup is Bob.
    lambda data: data.index('hip hop') + 1 == data.index('Kailyn'),  # The person who loves hip-hop music is directly left of The person whose mother's name is Kailyn.
    lambda data: data.index('Arnold') > data.index('Kailyn'),  # Arnold is somewhere to the right of The person whose mother's name is Kailyn.
    lambda data: data.index('water') + 1 == data.index('blue master'),  # The one who only drinks water is directly left of the person who smokes Blue Master.
    lambda data: data.index('spaghetti') < data.index('blends'),  # The person who loves the spaghetti eater is somewhere to the left of the person who smokes many unique blends.
    lambda data: data.index('Sarah') + 1 == data.index('jazz'),  # The person whose mother's name is Sarah is directly left of the person who loves jazz music.
    lambda data: data.index('hip hop') + 1 == data.index('root beer'),  # The person who loves hip-hop music is directly left of the root beer lover.
    lambda data: data[data.index('water')][5] == 'stew',  # The one who only drinks water is the person who loves the stew.
    lambda data: data.index('dunhill') != 1,  # The Dunhill smoker is not in the second house.
    lambda data: data[data.index('milk')][6] == 'Janelle',  # The person who likes milk is The person whose mother's name is Janelle.
    lambda data: data[data.index('Eric')][6] == 'Aniya',  # Eric is The person whose mother's name is Aniya.
]

# Lists of possible values for each category
names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
music_genres = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

# Generate all possible permutations
permutations = list(itertools.permutations(range(6)))

def is_valid(data):
    # Check all constraints
    for constraint in constraints:
        if not constraint(data):
            return False
    return True

def solve():
    for name_perm in permutations:
        for cigar_perm in permutations:
            for music_genre_perm in permutations:
                for drink_perm in permutations:
                    for mother_perm in permutations:
                        for food_perm in permutations:
                            data = []
                            for i in range(6):
                                data.append([names[name_perm[i]], cigars[cigar_perm[i]], music_genres[music_genre_perm[i]],
                                             drinks[drink_perm[i]], mothers[mother_perm[i]], foods[food_perm[i]]])
                            
                            if is_valid(data):
                                # Format the solution as JSON
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                        "rows": [[str(i+1)] + row for i, row in enumerate(data)]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Solve the puzzle
print(solve())