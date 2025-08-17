import itertools
import json

def solve_puzzle():
    # Define the lists of attributes
    names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    favorite_sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    # Check each permutation against the clues
    for perm in all_permutations:
        name_order = [names[i] for i in perm]
        animal_order = [animals[i] for i in perm]
        occupation_order = [occupations[i] for i in perm]
        favorite_sport_order = [favorite_sports[i] for i in perm]
        height_order = [heights[i] for i in perm]

        # Clue 1: The person who is an engineer is the dog owner.
        if occupation_order.index("engineer") != animal_order.index("dog"):
            continue

        # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
        if height_order.index("average") >= height_order.index("short"):
            continue

        # Clue 3: The person who has an average height is directly left of the rabbit owner.
        if height_order.index("average") + 1 != animal_order.index("rabbit"):
            continue

        # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
        if height_order.index("tall") >= height_order.index("very short"):
            continue

        # Clue 5: Arnold is the cat lover.
        if name_order.index("Arnold") != animal_order.index("cat"):
            continue

        # Clue 6: The person who keeps horses is the person who is a teacher.
        if animal_order.index("horse") != occupation_order.index("teacher"):
            continue

        # Clue 7: Carol is the person who loves soccer.
        if name_order.index("Carol") != favorite_sport_order.index("soccer"):
            continue

        # Clue 8: The person who is tall is the person who loves volleyball.
        if height_order.index("tall") != favorite_sport_order.index("volleyball"):
            continue

        # Clue 9: The person who is a lawyer is in the fifth house.
        if occupation_order[4] != "lawyer":
            continue

        # Clue 10: The person who loves tennis is the person who is a teacher.
        if favorite_sport_order.index("tennis") != occupation_order.index("teacher"):
            continue

        # Clue 11: The person who has an average height is the person who loves swimming.
        if height_order.index("average") != favorite_sport_order.index("swimming"):
            continue

        # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
        if favorite_sport_order.index("baseball") + 1 != occupation_order.index("engineer"):
            continue

        # Clue 13: Peter is the person who is a nurse.
        if name_order.index("Peter") != occupation_order.index("nurse"):
            continue

        # Clue 14: Bob is somewhere to the right of the person who is an artist.
        if name_order.index("Bob") <= occupation_order.index("artist"):
            continue

        # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
        if occupation_order.index("teacher") + 1 != favorite_sport_order.index("soccer"):
            continue

        # Clue 16: The rabbit owner is Alice.
        if animal_order.index("rabbit") != name_order.index("Alice"):
            continue

        # Clue 17: The fish enthusiast is Carol.
        if animal_order.index("fish") != name_order.index("Carol"):
            continue

        # Clue 18: The person who loves baseball is in the first house.
        if favorite_sport_order[0] != "baseball":
            continue

        # Clue 19: The cat lover is somewhere to the right of the person who is very short.
        if name_order.index("Arnold") <= height_order.index("very short"):
            continue

        # Clue 20: The person who is super tall is in the fifth house.
        if height_order[4] != "super tall":
            continue

        # If all clues are satisfied, construct the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": []
            }
        }

        for i in range(6):
            solution["solution"]["rows"].append([
                str(i + 1),
                name_order[i],
                animal_order[i],
                occupation_order[i],
                favorite_sport_order[i],
                height_order[i]
            ])

        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())