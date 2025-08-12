import itertools
import json

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    # Check each permutation against the clues
    for name_order in permutations:
        for style_order in permutations:
            for music_order in permutations:
                for hobby_order in permutations:
                    # Unpack the permutations for easier access
                    name_map = {name: i for i, name in enumerate(name_order)}
                    style_map = {style: i for i, style in enumerate(style_order)}
                    music_map = {music: i for i, music in enumerate(music_order)}
                    hobby_map = {hobby: i for i, hobby in enumerate(hobby_order)}

                    # Apply the clues
                    if (
                        # Clue 1
                        music_map["rock"] == 4 and
                        # Clue 2
                        abs(style_map["victorian"] - hobby_map["woodworking"]) == 1 and
                        # Clue 3
                        music_map["hip hop"] == style_map["mediterranean"] and
                        # Clue 4
                        abs(name_map["Arnold"] - style_map["victorian"]) == 2 and
                        # Clue 5
                        music_map["jazz"] == name_map["Eric"] - 1 and
                        # Clue 6
                        music_map["hip hop"] < hobby_map["knitting"] and
                        # Clue 7
                        music_map["hip hop"] == name_map["Carol"] and
                        # Clue 8
                        style_map["craftsman"] == name_map["Arnold"] and
                        # Clue 9
                        style_map["ranch"] == name_map["Eric"] and
                        # Clue 10
                        style_map["victorian"] == hobby_map["woodworking"] and
                        # Clue 11
                        music_map["country"] == 0 and
                        # Clue 12
                        abs(hobby_map["painting"] - style_map["colonial"]) == 1 and
                        # Clue 13
                        hobby_map["photography"] == name_map["Alice"] and
                        # Clue 14
                        hobby_map["gardening"] == name_map["Eric"] and
                        # Clue 15
                        name_map["Bob"] == 2
                    ):
                        # If all clues are satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "House Style", "Music Genre", "Hobby"],
                                "rows": []
                            }
                        }
                        for house in range(6):
                            solution["solution"]["rows"].append([
                                str(house + 1),
                                names[name_order[house]],
                                house_styles[style_order[house]],
                                music_genres[music_order[house]],
                                hobbies[hobby_order[house]]
                            ])
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())