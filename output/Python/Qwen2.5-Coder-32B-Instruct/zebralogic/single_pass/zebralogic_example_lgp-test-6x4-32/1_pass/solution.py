import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names))
    permutations.extend(list(itertools.permutations(house_styles)))
    permutations.extend(list(itertools.permutations(music_genres)))
    permutations.extend(list(itertools.permutations(hobbies)))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(name_perm, style_perm, music_perm, hobby_perm):
        # Unpack the permutations into individual lists
        eric, alice, arnold, carol, peter, bob = name_perm
        mediterranean, modern, craftsman, ranch, colonial, victorian = style_perm
        country, hip_hop, pop, jazz, classical, rock = music_perm
        cooking, painting, photography, woodworking, gardening, knitting = hobby_perm

        # Check each clue
        if rock != music_perm[4]:
            return False
        if abs(classical - woodworking) != 1:
            return False
        if hip_hop != music_perm[name_perm.index(carol)]:
            return False
        if abs(arnold - victorian) != 3:
            return False
        if jazz != music_perm[name_perm.index(eric) - 1]:
            return False
        if hip_hop > knitting:
            return False
        if carol != name_perm[music_perm.index(hip_hop)]:
            return False
        if arnold != name_perm[style_perm.index(craftsman)]:
            return False
        if eric != name_perm[style_perm.index(ranch)]:
            return False
        if woodworking != hobby_perm[style_perm.index(victorian)]:
            return False
        if country != music_perm[0]:
            return False
        if abs(painting - colonial) != 1:
            return False
        if alice != name_perm[hobby_perm.index(photography)]:
            return False
        if gardening != hobby_perm[name_perm.index(eric)]:
            return False
        if bob != name_perm[2]:
            return False

        return True

    # Iterate over all possible combinations of permutations
    for name_perm in permutations[:720]:  # 6!
        for style_perm in permutations[720:1440]:  # Next 6!
            for music_perm in permutations[1440:2160]:  # Next 6!
                for hobby_perm in permutations[2160:2880]:  # Last 6!
                    if is_valid_solution(name_perm, style_perm, music_perm, hobby_perm):
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
                                name_perm[i],
                                style_perm[i],
                                music_perm[i],
                                hobby_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())