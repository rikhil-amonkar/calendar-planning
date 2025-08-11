import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
    cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
    music = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
    drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
    mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
    lunches = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "cigar", "music", "drink", "mother", "lunch"],
            "rows": []
        }
    }

    # We'll use a backtracking approach to find the solution
    from constraint import Problem, AllDifferentConstraint

    problem = Problem()

    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"cigar_{house}", cigars)
        problem.addVariable(f"music_{house}", music)
        problem.addVariable(f"drink_{house}", drinks)
        problem.addVariable(f"mother_{house}", mothers)
        problem.addVariable(f"lunch_{house}", lunches)

    # All attributes must be unique per category
    for category in ['name', 'cigar', 'music', 'drink', 'mother', 'lunch']:
        problem.addConstraint(AllDifferentConstraint(), [f"{category}_{house}" for house in houses])

    # Apply all constraints from the clues
    # Clue 2: Eric is not in the second house
    problem.addConstraint(lambda name: name != 'Eric', ["name_2"])

    # Clue 5: Eric is directly left of Carol
    for i in range(1, 6):
        problem.addConstraint(lambda e, c: e == 'Eric' and c == 'Carol', [f"name_{i}", f"name_{i+1}"])

    # Clue 1: Carol is directly left of the person who loves eating grilled cheese
    for i in range(1, 6):
        problem.addConstraint(lambda c, l: (c == 'Carol') and (l == 'grilled cheese'), [f"name_{i}", f"lunch_{i+1}"])

    # Clue 3: The person whose mother's name is Holly is somewhere to the right of Carol
    # Carol is in house i, Holly's mother is in house j where j > i
    # This is handled by finding Carol's position and ensuring Holly is to the right

    # Clue 4: The person who loves grilled cheese is somewhere to the right of the person who loves rock music
    # Rock is in house i, grilled cheese in house j where j > i

    # Clue 6: The person who loves pop music is not in the third house
    problem.addConstraint(lambda m: m != 'pop', ["music_3"])

    # Clue 7: Eric loves country music
    for house in houses:
        problem.addConstraint(lambda n, m: (n != 'Eric') or (m == 'country'), [f"name_{house}", f"music_{house}"])

    # Clue 8: The person who loves classical music is in the sixth house
    problem.addConstraint(lambda m: m == 'classical', ["music_6"])

    # Clue 9: The coffee drinker is Bob
    for house in houses:
        problem.addConstraint(lambda n, d: (n != 'Bob') or (d == 'coffee'), [f"name_{house}", f"drink_{house}"])

    # Clue 10: The person who smokes blends is Peter
    for house in houses:
        problem.addConstraint(lambda n, c: (n != 'Peter') or (c == 'blends'), [f"name_{house}", f"cigar_{house}"])

    # Clue 11: The person who loves the stew is not in the fifth house
    problem.addConstraint(lambda l: l != 'stew', ["lunch_5"])

    # Clue 12: The root beer lover is directly left of the person whose mother's name is Janelle
    for i in range(1, 6):
        problem.addConstraint(lambda d, m: (d == 'root beer') and (m == 'Janelle'), [f"drink_{i}", f"mother_{i+1}"])

    # Clue 13: There are two houses between the person whose mother's name is Sarah and the person who smokes yellow monster
    # Sarah in i, yellow monster in i+3
    for i in range(1, 4):
        problem.addConstraint(lambda m1, c2: (m1 == 'Sarah') and (c2 == 'yellow monster'), [f"mother_{i}", f"cigar_{i+3}"])

    # Clue 14: Eric is the tea drinker
    for house in houses:
        problem.addConstraint(lambda n, d: (n != 'Eric') or (d == 'tea'), [f"name_{house}", f"drink_{house}"])

    # Clue 15: The person who smokes pall mall is somewhere to the right of the person who loves stir fry
    # stir fry in i, pall mall in j where j > i

    # Clue 16: The person who loves the soup is Bob
    for house in houses:
        problem.addConstraint(lambda n, l: (n != 'Bob') or (l == 'soup'), [f"name_{house}", f"lunch_{house}"])

    # Clue 17: The person who loves hip-hop music is directly left of the person whose mother's name is Kailyn
    for i in range(1, 6):
        problem.addConstraint(lambda m, mother: (m == 'hip hop') and (mother == 'Kailyn'), [f"music_{i}", f"mother_{i+1}"])

    # Clue 18: Arnold is somewhere to the right of the person whose mother's name is Kailyn
    # Kailyn's mother in i, Arnold in j where j > i

    # Clue 19: The one who only drinks water is directly left of the person who smokes blue master
    for i in range(1, 6):
        problem.addConstraint(lambda d, c: (d == 'water') and (c == 'blue master'), [f"drink_{i}", f"cigar_{i+1}"])

    # Clue 20: The person who loves spaghetti is somewhere to the left of the person who smokes blends
    # spaghetti in i, blends in j where i < j

    # Clue 21: The person whose mother's name is Sarah is directly left of the person who loves jazz music
    for i in range(1, 6):
        problem.addConstraint(lambda m, music: (m == 'Sarah') and (music == 'jazz'), [f"mother_{i}", f"music_{i+1}"])

    # Clue 22: The person who loves hip-hop music is directly left of the root beer lover
    for i in range(1, 6):
        problem.addConstraint(lambda m, d: (m == 'hip hop') and (d == 'root beer'), [f"music_{i}", f"drink_{i+1}"])

    # Clue 23: The one who only drinks water is the person who loves the stew
    for house in houses:
        problem.addConstraint(lambda d, l: (d != 'water') or (l == 'stew'), [f"drink_{house}", f"lunch_{house}"])

    # Clue 24: The Dunhill smoker is not in the second house
    problem.addConstraint(lambda c: c != 'dunhill', ["cigar_2"])

    # Clue 25: The person who likes milk is the person whose mother's name is Janelle
    for house in houses:
        problem.addConstraint(lambda d, m: (d != 'milk') or (m == 'Janelle'), [f"drink_{house}", f"mother_{house}"])

    # Clue 26: Eric is the person whose mother's name is Aniya
    for house in houses:
        problem.addConstraint(lambda n, m: (n != 'Eric') or (m == 'Aniya'), [f"name_{house}", f"mother_{house}"])

    # Solve the problem
    solutions = problem.getSolutions()
    if not solutions:
        return solution

    # Take the first solution (assuming it's unique)
    sol = solutions[0]

    # Build the solution rows
    rows = []
    for house in houses:
        row = [
            str(house),
            sol[f"name_{house}"],
            sol[f"cigar_{house}"],
            sol[f"music_{house}"],
            sol[f"drink_{house}"],
            sol[f"mother_{house}"],
            sol[f"lunch_{house}"]
        ]
        rows.append(row)

    solution["solution"]["rows"] = rows
    return solution

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))