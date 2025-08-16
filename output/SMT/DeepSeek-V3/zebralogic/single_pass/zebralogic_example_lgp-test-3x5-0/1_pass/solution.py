from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the attributes
    names = ['Peter', 'Arnold', 'Eric']
    genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']

    # Create variables for each attribute in each house
    name = {h: String(f'name_{h}') for h in houses}
    genre = {h: String(f'genre_{h}') for h in houses}
    smoothie = {h: String(f'smoothie_{h}') for h in houses}
    birthday = {h: String(f'birthday_{h}') for h in houses}
    height = {h: String(f'height_{h}') for h in houses}

    # Add constraints that each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([genre[h] == g for g in genres]))
        s.add(Or([smoothie[h] == sm for sm in smoothies]))
        s.add(Or([birthday[h] == b for b in birthdays]))
        s.add(Or([height[h] == ht for ht in heights]))

    # Add uniqueness constraints for each attribute across houses
    for attr in [name, genre, smoothie, birthday, height]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Add clues as constraints
    # Clue 1: The person who likes Cherry smoothies is not in the second house.
    s.add(smoothie[2] != 'cherry')

    # Clue 2: Arnold is the person who loves mystery books.
    for h in houses:
        s.add(Implies(name[h] == 'Arnold', genre[h] == 'mystery'))

    # Clue 3: The person whose birthday is in January is not in the first house.
    s.add(birthday[1] != 'jan')

    # Clue 4: The person who is very short is the person who loves romance books.
    for h in houses:
        s.add(Implies(height[h] == 'very short', genre[h] == 'romance'))

    # Clue 5: The person who loves mystery books is the person whose birthday is in September.
    for h in houses:
        s.add(Implies(genre[h] == 'mystery', birthday[h] == 'sept'))

    # Clue 6: The person who has an average height is the Desert smoothie lover.
    for h in houses:
        s.add(Implies(height[h] == 'average', smoothie[h] == 'desert'))

    # Clue 7: Eric is in the first house.
    s.add(name[1] == 'Eric')

    # Clue 8: The Watermelon smoothie lover is the person who is short.
    for h in houses:
        s.add(Implies(smoothie[h] == 'watermelon', height[h] == 'short'))

    # Clue 9: The Watermelon smoothie lover is Eric.
    for h in houses:
        s.add(Implies(name[h] == 'Eric', smoothie[h] == 'watermelon'))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                model.evaluate(name[h]).as_string(),
                model.evaluate(genre[h]).as_string(),
                model.evaluate(smoothie[h]).as_string(),
                model.evaluate(birthday[h]).as_string(),
                model.evaluate(height[h]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution in JSON format
import json
print(json.dumps(solve_scheduling_problem(), indent=2))