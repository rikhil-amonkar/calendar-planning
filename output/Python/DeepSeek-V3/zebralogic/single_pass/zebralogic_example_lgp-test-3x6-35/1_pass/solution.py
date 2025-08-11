import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        "House": ["1", "2", "3"],
        "Name": ["Eric", "Arnold", "Peter"],
        "Vacation": ["mountain", "city", "beach"],
        "Height": ["very short", "average", "short"],
        "Flower": ["carnations", "daffodils", "lilies"],
        "Hair Color": ["brown", "black", "blonde"],
        "Education": ["associate", "bachelor", "high school"]
    }

    # Generate all possible permutations for each category
    for names in permutations(categories["Name"]):
        for vacations in permutations(categories["Vacation"]):
            for heights in permutations(categories["Height"]):
                for flowers in permutations(categories["Flower"]):
                    for hair_colors in permutations(categories["Hair Color"]):
                        for educations in permutations(categories["Education"]):
                            # Assign each attribute to houses
                            solution = {
                                "1": {
                                    "Name": names[0],
                                    "Vacation": vacations[0],
                                    "Height": heights[0],
                                    "Flower": flowers[0],
                                    "Hair Color": hair_colors[0],
                                    "Education": educations[0]
                                },
                                "2": {
                                    "Name": names[1],
                                    "Vacation": vacations[1],
                                    "Height": heights[1],
                                    "Flower": flowers[1],
                                    "Hair Color": hair_colors[1],
                                    "Education": educations[1]
                                },
                                "3": {
                                    "Name": names[2],
                                    "Vacation": vacations[2],
                                    "Height": heights[2],
                                    "Flower": flowers[2],
                                    "Hair Color": hair_colors[2],
                                    "Education": educations[2]
                                }
                            }

                            # Check all clues
                            valid = True

                            # Clue 1: Peter is the person who has an average height.
                            peter_house = None
                            for house in solution:
                                if solution[house]["Name"] == "Peter":
                                    peter_house = house
                                    break
                            if peter_house is None or solution[peter_house]["Height"] != "average":
                                valid = False
                                continue

                            # Clue 2: The person who loves a bouquet of daffodils is Arnold.
                            arnold_house = None
                            for house in solution:
                                if solution[house]["Name"] == "Arnold":
                                    arnold_house = house
                                    break
                            if arnold_house is None or solution[arnold_house]["Flower"] != "daffodils":
                                valid = False
                                continue

                            # Clue 3: The person who is very short is not in the second house.
                            very_short_house = None
                            for house in solution:
                                if solution[house]["Height"] == "very short":
                                    very_short_house = house
                                    break
                            if very_short_house is None or very_short_house == "2":
                                valid = False
                                continue

                            # Clue 4: The person who loves beach vacations is in the first house.
                            if solution["1"]["Vacation"] != "beach":
                                valid = False
                                continue

                            # Clue 5: The person with a high school diploma is in the third house.
                            if solution["3"]["Education"] != "high school":
                                valid = False
                                continue

                            # Clue 6: The person who is short is somewhere to the right of the person who is very short.
                            short_house = None
                            for house in solution:
                                if solution[house]["Height"] == "short":
                                    short_house = house
                                    break
                            if very_short_house is None or short_house is None or int(short_house) <= int(very_short_house):
                                valid = False
                                continue

                            # Clue 7: The person who loves the bouquet of lilies is Eric.
                            eric_house = None
                            for house in solution:
                                if solution[house]["Name"] == "Eric":
                                    eric_house = house
                                    break
                            if eric_house is None or solution[eric_house]["Flower"] != "lilies":
                                valid = False
                                continue

                            # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            if solution[eric_house]["Education"] != "bachelor":
                                valid = False
                                continue

                            # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
                            city_house = None
                            for house in solution:
                                if solution[house]["Vacation"] == "city":
                                    city_house = house
                                    break
                            if city_house is None or int(city_house) <= int(peter_house):
                                valid = False
                                continue

                            # Clue 10: The person who has blonde hair is in the third house.
                            if solution["3"]["Hair Color"] != "blonde":
                                valid = False
                                continue

                            # Clue 11: The person who loves beach vacations is the person who has brown hair.
                            if solution["1"]["Hair Color"] != "brown":
                                valid = False
                                continue

                            if valid:
                                # Prepare the output
                                output = {
                                    "solution": {
                                        "header": ["House", "Name", "Vacation", "Height", "Flower", "Hair Color", "Education"],
                                        "rows": []
                                    }
                                }
                                for house in ["1", "2", "3"]:
                                    row = [house]
                                    row.append(solution[house]["Name"])
                                    row.append(solution[house]["Vacation"] if "Vacation" not in solution[house] else solution[house]["Vacation"])
                                    row.append(solution[house]["Height"])
                                    row.append(solution[house]["Flower"] if "Flower" in solution[house] else solution[house]["Flower"])
                                    row.append(solution[house]["Hair Color"])
                                    row.append(solution[house]["Education"])
                                    output["solution"]["rows"].append(row)
                                return output

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))