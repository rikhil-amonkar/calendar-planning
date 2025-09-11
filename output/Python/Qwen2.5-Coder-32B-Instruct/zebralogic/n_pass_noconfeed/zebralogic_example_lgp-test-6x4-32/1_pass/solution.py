import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(music_genres)) * \
                       list(itertools.permutations(hobbies))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, house_styles_perm, music_genres_perm, hobbies_perm):
        # Unpack the permutations for easier access
        name_to_house = {name: i for i, name in enumerate(names_perm)}
        house_style_to_house = {style: i for i, style in enumerate(house_styles_perm)}
        music_genre_to_house = {genre: i for i, genre in enumerate(music_genres_perm)}
        hobby_to_house = {hobby: i for i, hobby in enumerate(hobbies_perm)}

        # Check each clue
        if music_genre_to_house["rock"] != 4:
            return False
        if abs(music_genre_to_house["classical"] - hobby_to_house["woodworking"]) != 1:
            return False
        if house_style_to_house["mediterranean"] != music_genre_to_house["hip hop"]:
            return False
        if abs(name_to_house["Arnold"] - house_style_to_house["victorian"]) != 2:
            return False
        if music_genre_to_house["jazz"] != name_to_house["Eric"] - 1:
            return False
        if music_genre_to_house["hip hop"] > hobby_to_house["knitting"]:
            return False
        if names_perm[music_genre_to_house["hip hop"]] != "Carol":
            return False
        if house_style_to_house["craftsman"] != name_to_house["Arnold"]:
            return False
        if house_style_to_house["ranch"] != name_to_house["Eric"]:
            return False
        if hobby_to_house["woodworking"] != house_style_to_house["victorian"]:
            return False
        if music_genre_to_house["country"] != 0:
            return False
        if abs(hobby_to_house["painting"] - house_style_to_house["colonial"]) != 1:
            return False
        if hobbies_perm[name_to_house["Alice"]] != "photography":
            return False
        if hobby_to_house["gardening"] != name_to_house["Eric"]:
            return False
        if names_perm[2] != "Bob":
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for house_styles_perm in itertools.permutations(house_styles):
            for music_genres_perm in itertools.permutations(music_genres):
                for hobbies_perm in itertools.permutations(hobbies):
                    if is_valid_solution(names_perm, house_styles_perm, music_genres_perm, hobbies_perm):
                        # Construct the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                                "rows": []
                            }
                        }
                        for i in range(6):
                            solution["solution"]["rows"].append([
                                str(i + 1),
                                names_perm[i],
                                house_styles_perm[i],
                                music_genres_perm[i],
                                hobbies_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())