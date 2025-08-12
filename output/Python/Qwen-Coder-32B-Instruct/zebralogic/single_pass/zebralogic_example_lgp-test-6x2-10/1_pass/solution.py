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
            house_attributes = {house: {"Name": name, "Music": music} for house, name, music in zip(houses, name_perm, music_perm)}

            # Check all constraints
            if (house_attributes[house_attributes["Bob"]["House"] + 1]["Music"] == "jazz" and
                house_attributes["Eric"]["House"] < house_attributes[house_attributes["Music"] == "hip hop"]["House"] and
                house_attributes[6]["Name"] == "Carol" and
                abs(house_attributes["Eric"]["House"] - house_attributes[house_attributes["Music"] == "hip hop"]["House"]) == 1 and
                house_attributes[6]["Music"] == "country" and
                house_attributes["Arnold"]["House"] != 5 and
                house_attributes["Arnold"]["House"] > house_attributes[house_attributes["Music"] == "pop"]["House"] and
                house_attributes[house_attributes["Music"] == "pop"]["Name"] == "Peter" and
                house_attributes[3]["Music"] == "hip hop" and
                abs(house_attributes["Peter"]["House"] - house_attributes["Bob"]["House"]) == 2 and
                house_attributes[house_attributes["Music"] == "rock"]["House"] != 5):

                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Music"],
                        "rows": []
                    }
                }

                for house in houses:
                    solution["solution"]["rows"].append([
                        str(house),
                        house_attributes[house]["Name"],
                        house_attributes[house]["Music"]
                    ])

                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())