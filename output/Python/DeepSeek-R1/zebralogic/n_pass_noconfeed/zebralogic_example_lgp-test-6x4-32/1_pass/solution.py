import json

def main():
    # We have deduced the solution manually by applying the constraints.
    # Now we represent the solution in a structured format.
    solution = {
        "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
        "rows": [
            ["1", "Arnold", "craftsman", "country", "painting"],
            ["2", "Carol", "mediterranean", "hip hop", "cooking"],
            ["3", "Bob", "colonial", "classical", "knitting"],
            ["4", "Peter", "victorian", "jazz", "woodworking"],
            ["5", "Eric", "ranch", "rock", "gardening"],
            ["6", "Alice", "modern", "pop", "photography"]
        ]
    }
    
    # Verify the solution against all clues to ensure correctness.
    # This step is critical to ensure that the solution satisfies all constraints.
    if verify_solution(solution):
        output = {"solution": solution}
        print(json.dumps(output, indent=2))
    else:
        print("Error: The solution does not satisfy all constraints.")

def verify_solution(solution):
    # Convert the list of rows into a more accessible structure per house index.
    houses = [None]  # index 0 unused
    for row in solution["rows"]:
        house_index = int(row[0])
        name = row[1]
        house_style = row[2]
        music_genre = row[3]
        hobby = row[4]
        houses.append({
            "name": name,
            "house_style": house_style,
            "music_genre": music_genre,
            "hobby": hobby
        })
    
    # Clue 1: The person who loves rock music is in the fifth house.
    if houses[5]["music_genre"] != "rock":
        return False
    
    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    classical_house = None
    woodworking_house = None
    for i in range(1, 7):
        if houses[i]["music_genre"] == "classical":
            classical_house = i
        if houses[i]["hobby"] == "woodworking":
            woodworking_house = i
    if abs(classical_house - woodworking_house) != 1:
        return False
    
    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
    for i in range(1, 7):
        if houses[i]["house_style"] == "mediterranean":
            if houses[i]["music_genre"] != "hip hop":
                return False
        if houses[i]["music_genre"] == "hip hop":
            if houses[i]["house_style"] != "mediterranean":
                return False
    
    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
    arnold_house = None
    victorian_house = None
    for i in range(1, 7):
        if houses[i]["name"] == "Arnold":
            arnold_house = i
        if houses[i]["house_style"] == "victorian":
            victorian_house = i
    if abs(arnold_house - victorian_house) != 3:
        return False
    
    # Clue 5: The person who loves jazz music is directly left of Eric.
    jazz_house = None
    eric_house = None
    for i in range(1, 7):
        if houses[i]["music_genre"] == "jazz":
            jazz_house = i
        if houses[i]["name"] == "Eric":
            eric_house = i
    if jazz_house != eric_house - 1:
        return False
    
    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    hip_hop_house = None
    knitting_house = None
    for i in range(1, 7):
        if houses[i]["music_genre"] == "hip hop":
            hip_hop_house = i
        if houses[i]["hobby"] == "knitting":
            knitting_house = i
    if hip_hop_house >= knitting_house:
        return False
    
    # Clue 7: Carol is the person who loves hip-hop music.
    for i in range(1, 7):
        if houses[i]["name"] == "Carol":
            if houses[i]["music_genre"] != "hip hop":
                return False
        if houses[i]["music_genre"] == "hip hop":
            if houses[i]["name"] != "Carol":
                return False
    
    # Clue 8: The person in a Craftsman-style house is Arnold.
    for i in range(1, 7):
        if houses[i]["house_style"] == "craftsman":
            if houses[i]["name"] != "Arnold":
                return False
        if houses[i]["name"] == "Arnold":
            if houses[i]["house_style"] != "craftsman":
                return False
    
    # Clue 9: The person in a ranch-style home is Eric.
    for i in range(1, 7):
        if houses[i]["house_style"] == "ranch":
            if houses[i]["name"] != "Eric":
                return False
        if houses[i]["name"] == "Eric":
            if houses[i]["house_style"] != "ranch":
                return False
    
    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
    for i in range(1, 7):
        if houses[i]["hobby"] == "woodworking":
            if houses[i]["house_style"] != "victorian":
                return False
        if houses[i]["house_style"] == "victorian":
            if houses[i]["hobby"] != "woodworking":
                return False
    
    # Clue 11: The person who loves country music is in the first house.
    if houses[1]["music_genre"] != "country":
        return False
    
    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    painting_house = None
    colonial_house = None
    for i in range(1, 7):
        if houses[i]["hobby"] == "painting":
            painting_house = i
        if houses[i]["house_style"] == "colonial":
            colonial_house = i
    if abs(painting_house - colonial_house) != 2:
        return False
    
    # Clue 13: Alice is the photography enthusiast.
    for i in range(1, 7):
        if houses[i]["name"] == "Alice":
            if houses[i]["hobby"] != "photography":
                return False
        if houses[i]["hobby"] == "photography":
            if houses[i]["name"] != "Alice":
                return False
    
    # Clue 14: The person who enjoys gardening is Eric.
    for i in range(1, 7):
        if houses[i]["hobby"] == "gardening":
            if houses[i]["name"] != "Eric":
                return False
        if houses[i]["name"] == "Eric":
            if houses[i]["hobby"] != "gardening":
                return False
    
    # Clue 15: Bob is in the third house.
    if houses[3]["name"] != "Bob":
        return False
    
    return True

if __name__ == "__main__":
    main()