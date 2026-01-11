import itertools
import json

# Constants
HOUSE_NUMBERS = [1, 2, 3, 4, 5, 6]
NAMES = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
PETS = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
HOUSE_STYLES = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
BIRTHDAYS = ['mar', 'sept', 'may', 'feb', 'jan', 'april']

# Constraint functions
def constraint_1(state):
    hamster_index = next((i for i, house in enumerate(state) if house['pet'] == 'hamster'), None)
    march_index = next((i for i, house in enumerate(state) if house['birthday'] == 'mar'), None)
    return hamster_index is None or march_index is None or hamster_index > march_index

def constraint_2(state):
    jan_index = next((i for i, house in enumerate(state) if house['birthday'] == 'jan'), None)
    sept_index = next((i for i, house in enumerate(state) if house['birthday'] == 'sept'), None)
    return jan_index is None or sept_index is None or jan_index < sept_index

def constraint_3(state):
    return state[1]['birthday'] == 'may'

def constraint_4(state):
    return state[1]['house_style'] == 'colonial'

def constraint_5(state):
    return state[2]['name'] == 'Carol'

def constraint_6(state):
    return state[5]['house_style'] != 'mediterranean'

def constraint_7(state):
    bob_index = next((i for i, house in enumerate(state) if house['name'] == 'Bob'), None)
    fish_index = next((i for i, house in enumerate(state) if house['pet'] == 'fish'), None)
    return bob_index is None or fish_index is None or fish_index > bob_index

def constraint_8(state):
    return state[5]['name'] == 'Eric'

def constraint_9(state):
    victorian_index = next((i for i, house in enumerate(state) if house['house_style'] == 'victorian'), None)
    cat_index = next((i for i, house in enumerate(state) if house['pet'] == 'cat'), None)
    return victorian_index is None or cat_index is None or abs(victorian_index - cat_index) == 1

def constraint_10(state):
    victorian_index = next((i for i, house in enumerate(state) if house['house_style'] == 'victorian'), None)
    hamster_index = next((i for i, house in enumerate(state) if house['pet'] == 'hamster'), None)
    return victorian_index is None or hamster_index is None or abs(victorian_index - hamster_index) == 2

def constraint_11(state):
    return state[3]['house_style'] == 'craftsman'

def constraint_12(state):
    colonial_index = next((i for i, house in enumerate(state) if house['house_style'] == 'colonial'), None)
    modern_index = next((i for i, house in enumerate(state) if house['house_style'] == 'modern'), None)
    return colonial_index is None or modern_index is None or colonial_index < modern_index

def constraint_13(state):
    return state[1]['pet'] != 'fish'

def constraint_14(state):
    return state[1]['name'] == 'Peter'

def constraint_15(state):
    jan_index = next((i for i, house in enumerate(state) if house['birthday'] == 'jan'), None)
    april_index = next((i for i, house in enumerate(state) if house['birthday'] == 'april'), None)
    return jan_index is None or april_index is None or jan_index + 1 == april_index

def constraint_16(state):
    modern_index = next((i for i, house in enumerate(state) if house['house_style'] == 'modern'), None)
    bird_index = next((i for i, house in enumerate(state) if house['pet'] == 'bird'), None)
    return modern_index is None or bird_index is None or abs(modern_index - bird_index) == 1

def constraint_17(state):
    return state[2]['birthday'] == 'mar'

def constraint_18(state):
    return state[3]['house_style'] == 'craftsman'

def constraint_19(state):
    return state[3]['pet'] == 'dog'

def check_constraints(state):
    return (constraint_1(state) and constraint_2(state) and constraint_3(state) and constraint_4(state) and
            constraint_5(state) and constraint_6(state) and constraint_7(state) and constraint_8(state) and
            constraint_9(state) and constraint_10(state) and constraint_11(state) and constraint_12(state) and
            constraint_13(state) and constraint_14(state) and constraint_15(state) and constraint_16(state) and
            constraint_17(state) and constraint_18(state) and constraint_19(state))

# Generate all permutations and check constraints
def solve_puzzle():
    for name_perm in itertools.permutations(NAMES):
        for pet_perm in itertools.permutations(PETS):
            for house_style_perm in itertools.permutations(HOUSE_STYLES):
                for birthday_perm in itertools.permutations(BIRTHDAYS):
                    state = [{'name': name_perm[i], 'pet': pet_perm[i], 'house_style': house_style_perm[i], 'birthday': birthday_perm[i]} for i in range(6)]
                    if check_constraints(state):
                        return format_solution(state)
    return None

def format_solution(state):
    rows = []
    for i, house in enumerate(state):
        rows.append([str(i+1), house['name'], house['pet'], house['house_style'], house['birthday']])
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": rows
        }
    }
    return json.dumps(solution_dict, indent=2)

# Solve and print the puzzle
solution = solve_puzzle()
print(solution)