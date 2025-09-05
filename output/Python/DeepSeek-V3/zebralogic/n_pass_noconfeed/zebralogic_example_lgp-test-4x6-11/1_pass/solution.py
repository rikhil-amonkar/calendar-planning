import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthdays = ['april', 'jan', 'sept', 'feb']
    music_genres = ['pop', 'rock', 'classical', 'jazz']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for animal_perm in permutations(animals):
                for book_perm in permutations(book_genres):
                    for birthday_perm in permutations(birthdays):
                        for music_perm in permutations(music_genres):
                            # Create assignment dictionaries for each house
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'Hobby': hobby_perm[i],
                                    'Animal': animal_perm[i],
                                    'BookGenre': book_perm[i],
                                    'Birthday': birthday_perm[i],
                                    'MusicGenre': music_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # 1. The person who loves cooking is the person who loves romance books.
                            for house in houses:
                                if assignment[house]['Hobby'] == 'cooking':
                                    if assignment[house]['BookGenre'] != 'romance':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 2. The person whose birthday is in February is the person who loves pop music.
                            for house in houses:
                                if assignment[house]['Birthday'] == 'feb':
                                    if assignment[house]['MusicGenre'] != 'pop':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 3. Eric is not in the second house.
                            if assignment[2]['Name'] == 'Eric':
                                valid = False
                            
                            if not valid:
                                continue
                            
                            # 4. The person who loves romance books is not in the fourth house.
                            for house in houses:
                                if assignment[house]['BookGenre'] == 'romance':
                                    if house == 4:
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 5. The person whose birthday is in February is the fish enthusiast.
                            for house in houses:
                                if assignment[house]['Birthday'] == 'feb':
                                    if assignment[house]['Animal'] != 'fish':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 6. Alice is somewhere to the right of the person who loves fantasy books.
                            alice_house = None
                            fantasy_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Alice':
                                    alice_house = house
                                if assignment[house]['BookGenre'] == 'fantasy':
                                    fantasy_house = house
                            
                            if alice_house is None or fantasy_house is None or alice_house <= fantasy_house:
                                valid = False
                            
                            if not valid:
                                continue
                            
                            # 7. The person who keeps horses is the person who loves rock music.
                            for house in houses:
                                if assignment[house]['Animal'] == 'horse':
                                    if assignment[house]['MusicGenre'] != 'rock':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 8. The person who enjoys gardening is the person whose birthday is in April.
                            for house in houses:
                                if assignment[house]['Hobby'] == 'gardening':
                                    if assignment[house]['Birthday'] != 'april':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 9. The person who loves jazz music is the person who loves cooking.
                            for house in houses:
                                if assignment[house]['MusicGenre'] == 'jazz':
                                    if assignment[house]['Hobby'] != 'cooking':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 10. The person who loves rock music is the person who loves mystery books.
                            for house in houses:
                                if assignment[house]['MusicGenre'] == 'rock':
                                    if assignment[house]['BookGenre'] != 'mystery':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 11. The person who paints as a hobby is directly left of the person who loves romance books.
                            painting_house = None
                            romance_house = None
                            for house in houses:
                                if assignment[house]['Hobby'] == 'painting':
                                    painting_house = house
                                if assignment[house]['BookGenre'] == 'romance':
                                    romance_house = house
                            
                            if painting_house is None or romance_house is None or romance_house - painting_house != 1:
                                valid = False
                            
                            if not valid:
                                continue
                            
                            # 12. Peter is the person who loves pop music.
                            for house in houses:
                                if assignment[house]['Name'] == 'Peter':
                                    if assignment[house]['MusicGenre'] != 'pop':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 13. The person who enjoys gardening is Arnold.
                            for house in houses:
                                if assignment[house]['Hobby'] == 'gardening':
                                    if assignment[house]['Name'] != 'Arnold':
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 14. The person who loves rock music is directly left of the person whose birthday is in January.
                            rock_house = None
                            jan_house = None
                            for house in houses:
                                if assignment[house]['MusicGenre'] == 'rock':
                                    rock_house = house
                                if assignment[house]['Birthday'] == 'jan':
                                    jan_house = house
                            
                            if rock_house is None or jan_house is None or jan_house - rock_house != 1:
                                valid = False
                            
                            if not valid:
                                continue
                            
                            # 15. The person who loves cooking is not in the third house.
                            for house in houses:
                                if assignment[house]['Hobby'] == 'cooking':
                                    if house == 3:
                                        valid = False
                                        break
                            
                            if not valid:
                                continue
                            
                            # 16. The cat lover is somewhere to the right of the person who keeps horses.
                            cat_house = None
                            horse_house = None
                            for house in houses:
                                if assignment[house]['Animal'] == 'cat':
                                    cat_house = house
                                if assignment[house]['Animal'] == 'horse':
                                    horse_house = house
                            
                            if cat_house is None or horse_house is None or cat_house <= horse_house:
                                valid = False
                            
                            if not valid:
                                continue
                            
                            # If we get here, we found a valid solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                    "rows": []
                                }
                            }
                            
                            for house in sorted(assignment.keys()):
                                row = [
                                    str(house),
                                    assignment[house]['Name'],
                                    assignment[house]['Hobby'],
                                    assignment[house]['Animal'],
                                    assignment[house]['BookGenre'],
                                    assignment[house]['Birthday'],
                                    assignment[house]['MusicGenre']
                                ]
                                result["solution"]["rows"].append(row)
                            
                            print(json.dumps(result, indent=2))
                            return
    
    print("No solution found")

if __name__ == "__main__":
    main()