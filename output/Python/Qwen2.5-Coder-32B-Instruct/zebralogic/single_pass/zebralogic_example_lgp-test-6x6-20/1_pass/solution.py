import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_genres = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    foods = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for music_genre_perm in itertools.permutations(music_genres):
                for drink_perm in itertools.permutations(drinks):
                    for mother_perm in itertools.permutations(mothers):
                        for food_perm in itertools.permutations(foods):
                            # Create a dictionary to store the assignment
                            assignment = {house: {} for house in houses}
                            for i in range(6):
                                assignment[houses[i]]["Name"] = name_perm[i]
                                assignment[houses[i]]["Cigar"] = cigar_perm[i]
                                assignment[houses[i]]["MusicGenre"] = music_genre_perm[i]
                                assignment[houses[i]]["Drink"] = drink_perm[i]
                                assignment[houses[i]]["Mother"] = mother_perm[i]
                                assignment[houses[i]]["Food"] = food_perm[i]

                            # Check constraints
                            if (name_perm.index("Carol") + 1 == name_perm.index("grilled cheese") and
                                name_perm.index("Eric") != 1 and
                                mother_perm.index("Holly") > name_perm.index("Carol") and
                                food_perm.index("grilled cheese") > music_genre_perm.index("rock") and
                                name_perm.index("Eric") + 1 == name_perm.index("Carol") and
                                music_genre_perm.index("pop") != 2 and
                                name_perm[name_perm.index("Eric")] == "country" and
                                music_genre_perm[5] == "classical" and
                                drink_perm.index("coffee") == name_perm.index("Bob") and
                                cigar_perm.index("blends") == name_perm.index("Peter") and
                                food_perm.index("stew") != 4 and
                                drink_perm.index("root beer") + 1 == mother_perm.index("Janelle") and
                                abs(mother_perm.index("Sarah") - cigar_perm.index("yellow monster")) == 3 and
                                drink_perm.index("tea") == name_perm.index("Eric") and
                                cigar_perm.index("pall mall") > food_perm.index("stir fry") and
                                food_perm.index("soup") == name_perm.index("Bob") and
                                music_genre_perm.index("hip hop") + 1 == mother_perm.index("Kailyn") and
                                name_perm.index("Arnold") > mother_perm.index("Kailyn") and
                                drink_perm.index("water") + 1 == cigar_perm.index("blue master") and
                                food_perm.index("spaghetti") < cigar_perm.index("blends") and
                                mother_perm.index("Sarah") + 1 == music_genre_perm.index("jazz") and
                                music_genre_perm.index("hip hop") + 1 == drink_perm.index("root beer") and
                                drink_perm.index("water") == food_perm.index("stew") and
                                cigar_perm.index("dunhill") != 1 and
                                drink_perm.index("milk") == mother_perm.index("Janelle") and
                                mother_perm.index("Aniya") == name_perm.index("Eric")):
                                
                                # If all constraints are satisfied, return the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                        "rows": []
                                    }
                                }
                                for house in houses:
                                    row = [str(house)]
                                    for key in solution["solution"]["header"][1:]:
                                        row.append(assignment[house][key])
                                    solution["solution"]["rows"].append(row)
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())