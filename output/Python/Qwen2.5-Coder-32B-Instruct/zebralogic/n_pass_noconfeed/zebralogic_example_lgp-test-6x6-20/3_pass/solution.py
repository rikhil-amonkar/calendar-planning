import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_genres = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    foods = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    # Function to check if a permutation satisfies all clues
    def is_valid(permutation):
        n, c, m, d, mo, f = permutation

        # Unpack the permutation into named variables for clarity
        name_order = [names[i] for i in permutation]
        cigar_order = [cigars[i] for i in permutation]
        music_genre_order = [music_genres[i] for i in permutation]
        drink_order = [drinks[i] for i in permutation]
        mother_order = [mothers[i] for i in permutation]
        food_order = [foods[i] for i in permutation]

        # Check each clue
        if not (name_order[n] == "Carol" and food_order[f] == "grilled cheese" and f == n + 1):
            return False
        if name_order[n] != "Eric" or n != 1:
            return False
        if mother_order[mo] == "Holly" and n >= f:
            return False
        if music_genre_order[m] == "rock" and f > m:
            return False
        if name_order[n] == "Eric" and abs(n - f) == 1:
            return False
        if music_genre_order[m] == "pop" and n != 2:
            return False
        if name_order[n] == "Eric" and music_genre_order[m] == "country":
            return False
        if music_genre_order[m] == "classical" and n != 5:
            return False
        if drink_order[d] == "coffee" and name_order[n] != "Bob":
            return False
        if cigar_order[c] == "blends" and name_order[n] != "Peter":
            return False
        if food_order[f] == "stew" and n != 4:
            return False
        if drink_order[d] == "root beer" and mother_order[mo] == "Janelle" and d != mo - 1:
            return False
        if abs(mother_order.index("Sarah") - cigar_order.index("yellow monster")) != 2:
            return False
        if name_order[n] == "Eric" and drink_order[d] == "tea":
            return False
        if cigar_order[c] == "pall mall" and food_order[f] == "stir fry" and c >= f:
            return False
        if food_order[f] == "soup" and name_order[n] != "Bob":
            return False
        if music_genre_order[m] == "hip hop" and mother_order[mo] == "Kailyn" and m != mo - 1:
            return False
        if name_order[n] == "Arnold" and mother_order[mo] == "Kailyn" and n >= mo:
            return False
        if drink_order[d] == "water" and cigar_order[c] == "blue master" and d != c - 1:
            return False
        if food_order[f] == "spaghetti" and cigar_order[c] == "blends" and f <= c:
            return False
        if mother_order[mo] == "Sarah" and music_genre_order[m] == "jazz" and mo != m - 1:
            return False
        if music_genre_order[m] == "hip hop" and drink_order[d] == "root beer" and m != d - 1:
            return False
        if drink_order[d] == "water" and food_order[f] == "stew" and d != f - 1:
            return False
        if cigar_order[c] == "dunhill" and n != 1:
            return False
        if drink_order[d] == "milk" and mother_order[mo] == "Janelle" and d != mo:
            return False
        if name_order[n] == "Eric" and mother_order[mo] == "Aniya" and n == mo:
            return False

        return True

    # Find the valid permutation
    solution_perm = None
    for perm in permutations:
        if is_valid(perm):
            solution_perm = perm
            break

    # Check if a valid permutation was found
    if solution_perm is None:
        return json.dumps({"error": "No valid solution found"}, indent=2)

    # Construct the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
            "rows": []
        }
    }

    for i in range(6):
        solution["solution"]["rows"].append([
            str(i + 1),
            names[solution_perm[i]],
            cigars[solution_perm[i]],
            music_genres[solution_perm[i]],
            drinks[solution_perm[i]],
            mothers[solution_perm[i]],
            foods[solution_perm[i]]
        ])

    return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())