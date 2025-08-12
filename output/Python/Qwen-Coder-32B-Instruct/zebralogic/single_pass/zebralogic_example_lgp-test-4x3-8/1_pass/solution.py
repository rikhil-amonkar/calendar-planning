import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names))
    permutations += list(itertools.permutations(hair_colors))
    permutations += list(itertools.permutations(music_genres))

    # Iterate over all possible combinations of permutations
    for names_perm in permutations[:len(names)]:
        for hair_colors_perm in permutations[len(names):2*len(names)]:
            for music_genres_perm in permutations[2*len(names):]:
                # Unpack the current permutation
                name_to_house = {name: i+1 for i, name in enumerate(names_perm)}
                hair_color_to_house = {color: i+1 for i, color in enumerate(hair_colors_perm)}
                music_genre_to_house = {genre: i+1 for i, genre in enumerate(music_genres_perm)}

                # Check all the clues
                if (name_to_house["Eric"] == hair_color_to_house["red"] and
                    music_genre_to_house["classical"] == hair_color_to_house["blonde"] - 1 and
                    hair_color_to_house["brown"] != 1 and
                    music_genre_to_house["pop"] != 3 and
                    music_genre_to_house["classical"] == 1 and
                    music_genre_to_house["jazz"] == hair_color_to_house["red"] and
                    music_genre_to_house["rock"] == name_to_house["Arnold"] and
                    name_to_house["Peter"] > music_genre_to_house["rock"]):
                    
                    # If all clues are satisfied, construct the solution
                    solution = []
                    for house in range(1, 5):
                        name = names_perm[house-1]
                        hair_color = hair_colors_perm[house-1]
                        music_genre = music_genres_perm[house-1]
                        solution.append([str(house), name, hair_color, music_genre])
                    
                    # Return the solution in the required format
                    return json.dumps({
                        "solution": {
                            "header": ["House", "Name", "Hair Color", "Favorite Music"],
                            "rows": solution
                        }
                    }, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())