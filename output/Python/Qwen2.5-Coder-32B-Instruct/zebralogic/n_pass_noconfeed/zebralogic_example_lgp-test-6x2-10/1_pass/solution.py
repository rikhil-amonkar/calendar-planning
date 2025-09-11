import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    music_genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for music_perm in itertools.permutations(music_genres):
            # Create a dictionary to map house number to attributes
            house_map = {house: {"Name": name, "MusicGenre": music}
                         for house, name, music in zip(houses, name_perm, music_perm)}

            # Check all constraints
            if (house_map[house_map["Bob"]["House"] + 1]["MusicGenre"] == "jazz" and
                house_map["Eric"]["House"] < house_map["hip hop"]["House"] and
                house_map[6]["Name"] == "Carol" and
                abs(house_map["Eric"]["House"] - house_map["hip hop"]["House"]) == 1 and
                house_map[6]["MusicGenre"] == "country" and
                house_map["Arnold"]["House"] != 5 and
                house_map["Arnold"]["House"] > house_map["pop"]["House"] and
                house_map["Peter"]["MusicGenre"] == "pop" and
                house_map[3]["MusicGenre"] == "hip hop" and
                abs(house_map["Peter"]["House"] - house_map["Bob"]["House"]) == 2 and
                house_map["rock"]["House"] != 5):

                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "MusicGenre"],
                        "rows": [[str(house), house_map[house]["Name"], house_map[house]["MusicGenre"]]
                                 for house in houses]
                    }
                }
                return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())