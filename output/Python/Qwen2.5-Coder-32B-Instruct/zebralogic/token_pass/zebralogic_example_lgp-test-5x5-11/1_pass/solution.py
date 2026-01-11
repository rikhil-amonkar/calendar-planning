import itertools
import json

# Define the attributes
names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
heights = ['average', 'very tall', 'very short', 'short', 'tall']
cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
phone_models = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']

# Define the constraints as functions
def constraint1(arrangement):
    # The Prince smoker is the Desert smoothie lover.
    return arrangement['prince'] == arrangement['desert']

def constraint2(arrangement):
    # There is one house between Eric and Alice.
    return abs(arrangement['Eric'] - arrangement['Alice']) == 2

def constraint3(arrangement):
    # The person who is short is the person who smokes many unique blends.
    return arrangement['short'] == arrangement['blends']

def constraint4(arrangement):
    # The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    return arrangement['iphone 13'] + 1 == arrangement['blue master']

def constraint5(arrangement):
    # The person who has an average height is the Dunhill smoker.
    return arrangement['average'] == arrangement['dunhill']

def constraint6(arrangement):
    # Eric is the person who is very tall.
    return arrangement['Eric'] == arrangement['very tall']

def constraint7(arrangement):
    # Arnold is directly left of the person who uses a Huawei P50.
    return arrangement['Arnold'] + 1 == arrangement['huawei p50']

def constraint8(arrangement):
    # Bob is not in the fourth house.
    return arrangement['Bob'] != 3

def constraint9(arrangement):
    # Eric is directly left of the person who likes Cherry smoothies.
    return arrangement['Eric'] + 1 == arrangement['cherry']

def constraint10(arrangement):
    # Bob is the Dunhill smoker.
    return arrangement['Bob'] == arrangement['dunhill']

def constraint11(arrangement):
    # The Dragonfruit smoothie lover is Bob.
    return arrangement['Bob'] == arrangement['dragonfruit']

def constraint12(arrangement):
    # The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    return abs(arrangement['iphone 13'] - arrangement['oneplus 9']) == 1

def constraint13(arrangement):
    # The person who uses a Samsung Galaxy S21 is the person who is short.
    return arrangement['samsung galaxy s21'] == arrangement['short']

def constraint14(arrangement):
    # There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    return abs(arrangement['very tall'] - arrangement['dragonfruit']) == 2

def constraint15(arrangement):
    # The person who uses an iPhone 13 is Eric.
    return arrangement['Eric'] == arrangement['iphone 13']

def constraint16(arrangement):
    # The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    return arrangement['desert'] < arrangement['lime']

def constraint17(arrangement):
    # Arnold and the person who is very short are next to each other.
    return abs(arrangement['Arnold'] - arrangement['very short']) == 1

# Function to check all constraints
def check_constraints(arrangement):
    constraints = [
        constraint1, constraint2, constraint3, constraint4, constraint5,
        constraint6, constraint7, constraint8, constraint9, constraint10,
        constraint11, constraint12, constraint13, constraint14, constraint15,
        constraint16, constraint17
    ]
    return all(constraint(arrangement) for constraint in constraints)

# Generate all permutations and find the valid one
for name_perm in itertools.permutations(names):
    for height_perm in itertools.permutations(heights):
        for cigar_perm in itertools.permutations(cigars):
            for smoothie_perm in itertools.permutations(smoothies):
                for phone_model_perm in itertools.permutations(phone_models):
                    arrangement = {
                        'Peter': name_perm[0], 'Arnold': name_perm[1], 'Eric': name_perm[2], 'Bob': name_perm[3], 'Alice': name_perm[4],
                        'average': height_perm[0], 'very tall': height_perm[1], 'very short': height_perm[2], 'short': height_perm[3], 'tall': height_perm[4],
                        'prince': cigar_perm[0], 'dunhill': cigar_perm[1], 'blends': cigar_perm[2], 'pall mall': cigar_perm[3], 'blue master': cigar_perm[4],
                        'lime': smoothie_perm[0], 'cherry': smoothie_perm[1], 'dragonfruit': smoothie_perm[2], 'watermelon': smoothie_perm[3], 'desert': smoothie_perm[4],
                        'oneplus 9': phone_model_perm[0], 'samsung galaxy s21': phone_model_perm[1], 'iphone 13': phone_model_perm[2], 'huawei p50': phone_model_perm[3], 'google pixel 6': phone_model_perm[4]
                    }
                    reverse_arrangement = {v: k for k, v in arrangement.items()}
                    if check_constraints(reverse_arrangement):
                        # Construct the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            house_number = str(i + 1)
                            name = name_perm[i]
                            height = reverse_arrangement[name]
                            cigar = reverse_arrangement[name]
                            smoothie = reverse_arrangement[name]
                            phone_model = reverse_arrangement[name]
                            solution["solution"]["rows"].append([
                                house_number,
                                name,
                                reverse_arrangement[name],
                                reverse_arrangement[name],
                                reverse_arrangement[name],
                                reverse_arrangement[name]
                            ])
                            solution["solution"]["rows"][-1][2] = reverse_arrangement[name_perm[i]]
                            solution["solution"]["rows"][-1][3] = reverse_arrangement[name_perm[i]]
                            solution["solution"]["rows"][-1][4] = reverse_arrangement[name_perm[i]]
                            solution["solution"]["rows"][-1][5] = reverse_arrangement[name_perm[i]]
                            solution["solution"]["rows"][-1][3] = reverse_arrangement[heights[i]]
                            solution["solution"]["rows"][-1][4] = reverse_arrangement[cigars[i]]
                            solution["solution"]["rows"][-1][5] = reverse_arrangement[smoothies[i]]
                            solution["solution"]["rows"][-1][5] = reverse_arrangement[phone_models[i]]
                        print(json.dumps(solution, indent=2))
                        break