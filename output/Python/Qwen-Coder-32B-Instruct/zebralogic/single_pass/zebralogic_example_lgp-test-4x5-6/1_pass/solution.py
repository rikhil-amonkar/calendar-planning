import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    musics = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(range(4)))

    # Iterate over all possible combinations of permutations
    for name_order in all_permutations:
        for education_order in all_permutations:
            for music_order in all_permutations:
                for color_order in all_permutations:
                    for flower_order in all_permutations:
                        # Create a dictionary to store the current assignment
                        assignment = {
                            "name": [names[i] for i in name_order],
                            "education": [educations[i] for i in education_order],
                            "music": [musics[i] for i in music_order],
                            "color": [colors[i] for i in color_order],
                            "flower": [flowers[i] for i in flower_order]
                        }

                        # Check all the clues
                        if (assignment["education"][assignment["flower"].index("daffodils")] == "bachelor" and
                            assignment["flower"].index("carnations") != 0 and
                            assignment["name"][assignment["education"].index("master")] == "Alice" and
                            assignment["flower"].index("carnations") == assignment["music"].index("classical") + 1 and
                            assignment["name"].index("Eric") != 1 and
                            assignment["name"].index("Arnold") != 2 and
                            assignment["color"].index("yellow") == assignment["flower"].index("roses") - 1 and
                            assignment["music"].index("pop") == 1 and
                            assignment["education"].index("associate") != 3 and
                            assignment["flower"].index("carnations") != 3 and
                            assignment["color"].index("red") == assignment["color"].index("white") - 1 and
                            assignment["music"][assignment["color"].index("red")] == "rock" and
                            assignment["name"][assignment["color"].index("yellow")] == "Arnold" and
                            assignment["color"].index("yellow") == assignment["flower"].index("daffodils")):
                            
                            # If all clues are satisfied, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "Music", "Color", "Flower"],
                                    "rows": []
                                }
                            }
                            for house in range(4):
                                solution["solution"]["rows"].append([
                                    str(house + 1),
                                    assignment["name"][house],
                                    assignment["education"][house],
                                    assignment["music"][house],
                                    assignment["color"][house],
                                    assignment["flower"][house]
                                ])
                            
                            # Print the solution as JSON
                            print(json.dumps(solution, indent=2))
                            return

# Run the function to solve the puzzle
solve_puzzle()