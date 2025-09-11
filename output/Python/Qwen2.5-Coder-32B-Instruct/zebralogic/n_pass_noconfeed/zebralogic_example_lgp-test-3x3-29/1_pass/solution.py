import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    people = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']
    houses = [1, 2, 3]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(people)) * list(itertools.permutations(mothers)) * list(itertools.permutations(foods))

    # Check each permutation against the clues
    for perm in permutations:
        person_order, mother_order, food_order = perm[:3], perm[3:6], perm[6:]
        if (abs(person_order.index('Peter') - food_order.index('spaghetti')) == 1 and
            food_order.index('grilled cheese') + 1 == mother_order.index('Aniya') and
            food_order.index('grilled cheese') == people.index('Eric') and
            person_order.index('Peter') == mother_order.index('Holly')):
            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Food"],
                    "rows": [
                        [str(houses[i]), person_order[i], mother_order[i], food_order[i]] for i in range(3)
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())