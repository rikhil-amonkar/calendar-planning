import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    books = ["science fiction", "romance", "mystery"]
    phones = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names))
    all_permutations.extend(list(itertools.permutations(cigars)))
    all_permutations.extend(list(itertools.permutations(animals)))
    all_permutations.extend(list(itertools.permutations(children)))
    all_permutations.extend(list(itertools.permutations(books)))
    all_permutations.extend(list(itertools.permutations(phones)))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(solution):
        # Unpack the solution into separate lists for each attribute
        names_sol, cigars_sol, animals_sol, children_sol, books_sol, phones_sol = solution

        # Check each clue
        if children_sol[books_sol.index("mystery")] != "Fred":
            return False
        if animals_sol[names_sol.index("Eric")] != "cat":
            return False
        if cigars_sol[1] != "pall mall":
            return False
        if children_sol[animals_sol.index("horse")] != "Meredith":
            return False
        if cigars_sol[children_sol.index("Bella")] != "prince":
            return False
        if phones_sol.index("iphone 13") + 1 != phones_sol.index("samsung galaxy s21"):
            return False
        if children_sol.index("Fred") + 1 != names_sol.index("Arnold"):
            return False
        if names_sol.index("Peter") >= names_sol.index("Eric"):
            return False
        if books_sol[phones_sol.index("samsung galaxy s21")] != "science fiction":
            return False
        if books_sol[2] != "science fiction":
            return False
        if books_sol[1] == "mystery":
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_sol in all_permutations[:6]:
        for cigars_sol in all_permutations[6:12]:
            for animals_sol in all_permutations[12:18]:
                for children_sol in all_permutations[18:24]:
                    for books_sol in all_permutations[24:30]:
                        for phones_sol in all_permutations[30:36]:
                            solution = [names_sol, cigars_sol, animals_sol, children_sol, books_sol, phones_sol]
                            if is_valid_solution(solution):
                                # Format the solution as required
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Favorite Cigar", "Animal", "Child", "Favorite Book", "Phone Model"],
                                        "rows": []
                                    }
                                }
                                for i in range(3):
                                    result["solution"]["rows"].append([
                                        str(i + 1),
                                        names_sol[i],
                                        cigars_sol[i],
                                        animals_sol[i],
                                        children_sol[i],
                                        books_sol[i],
                                        phones_sol[i]
                                    ])
                                return json.dumps(result, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())