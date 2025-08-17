import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    music_genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for music_perm in itertools.permutations(music_genres):
            # Unpack permutations for easier access
            bob_house = name_perm.index("Bob") + 1
            eric_house = name_perm.index("Eric") + 1
            carol_house = name_perm.index("Carol") + 1
            peter_house = name_perm.index("Peter") + 1
            jazz_house = music_perm.index("jazz") + 1
            pop_house = music_perm.index("pop") + 1
            classical_house = music_perm.index("classical") + 1
            rock_house = music_perm.index("rock") + 1
            hip_hop_house = music_perm.index("hip hop") + 1
            country_house = music_perm.index("country") + 1

            # Apply constraints
            if (bob_house + 1 == jazz_house and
                eric_house < hip_hop_house and
                carol_house == 6 and
                abs(eric_house - hip_hop_house) == 1 and
                country_house == carol_house and
                name_perm[4] != "Arnold" and
                arnold_house > pop_house and
                pop_house == peter_house and
                hip_hop_house == 3 and
                abs(peter_house - bob_house) == 2 and
                rock_house != 5):

                # Construct the solution
                solution = []
                for house in houses:
                    name = name_perm[house - 1]
                    music_genre = music_perm[house - 1]
                    solution.append([str(house), name, music_genre])

                return {
                    "solution": {
                        "header": ["House", "Name", "MusicGenre"],
                        "rows": solution
                    }
                }

# Solve the puzzle and print the solution as JSON
print(json.dumps(solve_puzzle(), indent=2))