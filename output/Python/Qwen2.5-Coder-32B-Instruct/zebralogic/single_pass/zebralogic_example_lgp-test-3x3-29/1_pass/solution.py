import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for food_perm in itertools.permutations(foods):
                # Unpack permutations for easier access
                name_house1, name_house2, name_house3 = name_perm
                mother_house1, mother_house2, mother_house3 = mother_perm
                food_house1, food_house2, food_house3 = food_perm

                # Apply clues
                if (abs(name_perm.index('Peter') - food_perm.index('spaghetti')) == 1 and
                    food_perm.index('grilled cheese') == name_perm.index('Eric') and
                    name_perm.index('Peter') == mother_perm.index('Holly') and
                    food_perm.index('grilled cheese') + 1 == mother_perm.index('Aniya')):
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Food"],
                            "rows": [
                                [str(houses[0]), name_house1, mother_house1, food_house1],
                                [str(houses[1]), name_house2, mother_house2, food_house2],
                                [str(houses[2]), name_house3, mother_house3, food_house3]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())