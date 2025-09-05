import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]
    
    # Initialize all possibilities
    from itertools import product
    possibilities = list(product(names, hobbies, book_genres, music_genres, birthdays))
    
    # Generate all possible assignments for both houses
    solutions = []
    for house1 in possibilities:
        for house2 in possibilities:
            # Check if all attributes are unique across houses
            if (len(set([house1[0], house2[0]])) == 2 and  # names
                len(set([house1[1], house2[1]])) == 2 and  # hobbies
                len(set([house1[2], house2[2]])) == 2 and  # book_genres
                len(set([house1[3], house2[3]])) == 2 and  # music_genres
                len(set([house1[4], house2[4]])) == 2):    # birthdays
                
                assignment = {1: house1, 2: house2}
                
                # Check all clues
                valid = True
                
                # Clue 1: The person who loves mystery books is the person who loves rock music.
                for house in [1, 2]:
                    if assignment[house][2] == "mystery" and assignment[house][3] != "rock":
                        valid = False
                        break
                
                # Clue 2: Arnold is not in the first house.
                if assignment[1][0] == "Arnold":
                    valid = False
                
                # Clue 3: The person who loves mystery books is the person who enjoys gardening.
                for house in [1, 2]:
                    if assignment[house][2] == "mystery" and assignment[house][1] != "gardening":
                        valid = False
                        break
                
                # Clue 4: The person whose birthday is in April is Arnold.
                for house in [1, 2]:
                    if assignment[house][4] == "april" and assignment[house][0] != "Arnold":
                        valid = False
                        break
                
                # Clue 5: The person who loves mystery books is in the first house.
                if assignment[1][2] != "mystery":
                    valid = False
                
                if valid:
                    solutions.append(assignment)
    
    # There should be exactly one solution
    if len(solutions) == 1:
        solution = solutions[0]
        
        # Format the output
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
        
        for house_num in sorted(solution.keys()):
            name, hobby, book_genre, music_genre, birthday = solution[house_num]
            result["solution"]["rows"].append([
                str(house_num),
                name,
                hobby,
                book_genre,
                music_genre,
                birthday
            ])
        
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No unique solution found"}, indent=2))

if __name__ == "__main__":
    main()