import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Peter', 'Arnold', 'Eric']
    genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    months = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for smoothie_perm in permutations(smoothies):
                for month_perm in permutations(months):
                    for height_perm in permutations(heights):
                        # Assign each permutation to houses
                        assignment = []
                        for i in range(3):
                            assignment.append({
                                'House': houses[i],
                                'Name': name_perm[i],
                                'book genre': genre_perm[i],
                                'favorite smoothie': smoothie_perm[i],
                                'birthday month': month_perm[i],
                                'height': height_perm[i]
                            })

                        # Check all constraints
                        valid = True

                        # Clue 7: Eric is in the first house
                        if assignment[0]['Name'] != 'Eric':
                            valid = False
                            continue

                        # Clue 2: Arnold loves mystery books
                        for house in assignment:
                            if house['Name'] == 'Arnold' and house['book genre'] != 'mystery':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 5: Mystery lover's birthday is in September
                        for house in assignment:
                            if house['book genre'] == 'mystery' and house['birthday month'] != 'sept':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 3: January birthday is not in first house
                        if assignment[0]['birthday month'] == 'jan':
                            valid = False
                            continue

                        # Clue 1: Cherry smoothie is not in second house
                        if assignment[1]['favorite smoothie'] == 'cherry':
                            valid = False
                            continue

                        # Clue 4: Very short person loves romance
                        for house in assignment:
                            if house['height'] == 'very short' and house['book genre'] != 'romance':
                                valid = False
                                break
                            if house['book genre'] == 'romance' and house['height'] != 'very short':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 6: Average height is desert smoothie
                        for house in assignment:
                            if house['height'] == 'average' and house['favorite smoothie'] != 'desert':
                                valid = False
                                break
                            if house['favorite smoothie'] == 'desert' and house['height'] != 'average':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 8: Watermelon lover is short
                        for house in assignment:
                            if house['favorite smoothie'] == 'watermelon' and house['height'] != 'short':
                                valid = False
                                break
                            if house['height'] == 'short' and house['favorite smoothie'] != 'watermelon':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 9: Watermelon lover is Eric
                        for house in assignment:
                            if house['Name'] == 'Eric' and house['favorite smoothie'] != 'watermelon':
                                valid = False
                                break
                            if house['favorite smoothie'] == 'watermelon' and house['Name'] != 'Eric':
                                valid = False
                                break
                        if not valid:
                            continue

                        # If all constraints are satisfied, prepare the solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "book genre", "favorite smoothie", "birthday month", "height"],
                                    "rows": []
                                }
                            }
                            for house in assignment:
                                solution["solution"]["rows"].append([
                                    house['House'],
                                    house['Name'],
                                    house['book genre'],
                                    house['favorite smoothie'],
                                    house['birthday month'],
                                    house['height']
                                ])
                            return solution

    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the JSON result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))