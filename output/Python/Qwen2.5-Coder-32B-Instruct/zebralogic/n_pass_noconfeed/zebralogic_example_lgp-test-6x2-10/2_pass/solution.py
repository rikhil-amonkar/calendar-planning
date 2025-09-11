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

            # Create reverse mappings for easier lookup
            name_to_house = {name: house for house, info in house_map.items() if "Name" in info and info["Name"] == name}
            music_to_house = {music: house for house, info in house_map.items() if "MusicGenre" in info and info["MusicGenre"] == music}

            # Check all constraints
            if (name_to_house.get("Bob") is not None and
                name_to_house.get("Bob") + 1 in house_map and
                house_map[name_to_house["Bob"] + 1]["MusicGenre"] == "jazz" and
                name_to_house.get("Eric") is not None and
                music_to_house.get("hip hop") is not None and
                name_to_house["Eric"] < music_to_house["hip hop"] and
                house_map[6]["Name"] == "Carol" and
                abs(name_to_house["Eric"] - music_to_house["hip hop"]) == 1 and
                house_map[6]["MusicGenre"] == "country" and
                name_to_house.get("Arnold") is not None and
                name_to_house["Arnold"] != 5 and
                name_to_house["Arnold"] > music_to_house.get("pop", 0) and
                name_to_house.get("Peter") is not None and
                house_map[name_to_house["Peter"]]["MusicGenre"] == "pop" and
                house_map[3]["MusicGenre"] == "hip hop" and
                abs(name_to_house["Peter"] - name_to_house["Bob"]) == 2 and
                music_to_house.get("rock") is not None and
                music_to_house["rock"] != 5):

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