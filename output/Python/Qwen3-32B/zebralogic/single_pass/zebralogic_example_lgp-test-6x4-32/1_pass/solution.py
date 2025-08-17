import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    house_styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    music_genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

    # Generate all possible name permutations where the third house is Bob
    valid_name_perms = []
    for name_perm in itertools.permutations(names):
        if name_perm[2] == 'Bob':  # house 3 (0-based index 2)
            valid_name_perms.append(name_perm)

    for name_perm in valid_name_perms:
        # Find positions of Arnold and Eric
        arnold_pos = name_perm.index('Arnold') + 1  # 1-based
        eric_pos = name_perm.index('Eric') + 1

        # Generate house style permutations where Arnold's house is craftsman and Eric's is ranch
        for house_style_perm in itertools.permutations(house_styles):
            if house_style_perm[arnold_pos - 1] == 'craftsman' and house_style_perm[eric_pos - 1] == 'ranch':
                # Find position of Victorian house
                victorian_pos = house_style_perm.index('victorian') + 1  # 1-based
                # Check constraint 4: Arnold and Victorian have two houses between
                if abs(arnold_pos - victorian_pos) == 3:
                    # Generate music genre permutations
                    for music_genre_perm in itertools.permutations(music_genres):
                        # Check constraint 11: house 1 is country, house 5 is rock
                        if music_genre_perm[0] == 'country' and music_genre_perm[4] == 'rock':
                            # Find Carol's position and check her music genre is hip hop
                            carol_pos = name_perm.index('Carol') + 1
                            if music_genre_perm[carol_pos - 1] == 'hip hop':
                                # Check constraint 5: jazz is directly left of Eric
                                if music_genre_perm[eric_pos - 2] == 'jazz':
                                    # Generate hobby permutations
                                    for hobby_perm in itertools.permutations(hobbies):
                                        # Check Eric's hobby is gardening
                                        if hobby_perm[eric_pos - 1] == 'gardening':
                                            # Check Alice's hobby is photography
                                            alice_pos = name_perm.index('Alice')
                                            if hobby_perm[alice_pos] == 'photography':
                                                # Check Victorian house has woodworking
                                                victorian_idx = house_style_perm.index('victorian')
                                                if hobby_perm[victorian_idx] == 'woodworking':
                                                    # Check constraint 6: hip hop (Carol's) is to the left of knitting
                                                    # Find position of 'knitting' in hobby_perm
                                                    try:
                                                        knitting_pos = hobby_perm.index('knitting') + 1
                                                        if carol_pos < knitting_pos:
                                                            # Check constraint 2: classical and woodworking are adjacent
                                                            classical_pos = [i for i, mg in enumerate(music_genre_perm) if mg == 'classical']
                                                            if classical_pos:
                                                                classical_pos = classical_pos[0] + 1  # 1-based
                                                                # Find position of woodworking in hobby_perm
                                                                woodworking_idx = house_style_perm.index('victorian')  # since woodworking is in victorian house
                                                                woodworking_pos = woodworking_idx + 1
                                                                # Check if classical is adjacent to woodworking_pos
                                                                if abs(classical_pos - woodworking_pos) == 1:
                                                                    # Check constraint 12: one house between painting and colonial
                                                                    # Find position of painting in hobby_perm
                                                                    painting_pos = hobby_perm.index('painting') + 1
                                                                    # Find position of colonial in house_style_perm
                                                                    colonial_pos = house_style_perm.index('colonial') + 1
                                                                    if abs(painting_pos - colonial_pos) == 2:
                                                                        # If all constraints are satisfied, build the solution
                                                                        solution = []
                                                                        for i in range(6):
                                                                            house_num = i + 1
                                                                            solution.append([
                                                                                str(house_num),
                                                                                name_perm[i],
                                                                                house_style_perm[i],
                                                                                music_genre_perm[i],
                                                                                hobby_perm[i]
                                                                            ])
                                                                        # Output the solution
                                                                        return {
                                                                            "solution": {
                                                                                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                                                                                "rows": solution
                                                                            }
                                                    except ValueError:
                                                        pass
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))