import itertools
import json

def main():
    attributes = [
        ['Peter', 'Alice', 'Eric', 'Arnold'],  # Name
        ['cooking', 'painting', 'gardening', 'photography'],  # Hobby
        ['horse', 'fish', 'cat', 'bird'],  # Animal
        ['fantasy', 'mystery', 'romance', 'science fiction'],  # BookGenre
        ['april', 'jan', 'sept', 'feb'],  # Birthday
        ['pop', 'rock', 'classical', 'jazz']  # MusicGenre
    ]
    
    def check_constraints(houses):
        # Constraint 1: cooking hobby and romance books are the same house.
        for house in houses:
            if house['Hobby'] == 'cooking' and house['BookGenre'] != 'romance':
                return False
            if house['BookGenre'] == 'romance' and house['Hobby'] != 'cooking':
                return False
        
        # Constraint 2: feb birthday and pop music are the same house.
        for house in houses:
            if house['Birthday'] == 'feb' and house['MusicGenre'] != 'pop':
                return False
            if house['MusicGenre'] == 'pop' and house['Birthday'] != 'feb':
                return False
        
        # Constraint 3 is already handled in the loop conditions.
        
        # Constraint 4 is already handled in the loop conditions.
        
        # Constraint 5: feb birthday and fish animal are the same house.
        for house in houses:
            if house['Birthday'] == 'feb' and house['Animal'] != 'fish':
                return False
            if house['Animal'] == 'fish' and house['Birthday'] != 'feb':
                return False
        
        # Constraint 6: Alice is to the right of fantasy books.
        fantasy_house = None
        alice_house = None
        for i, house in enumerate(houses):
            if house['BookGenre'] == 'fantasy':
                fantasy_house = i
            if house['Name'] == 'Alice':
                alice_house = i
        if fantasy_house is None or alice_house is None or alice_house <= fantasy_house:
            return False
        
        # Constraint 7: horse animal and rock music are the same house.
        for house in houses:
            if house['Animal'] == 'horse' and house['MusicGenre'] != 'rock':
                return False
            if house['MusicGenre'] == 'rock' and house['Animal'] != 'horse':
                return False
        
        # Constraint 8: gardening hobby and april birthday are the same house.
        for house in houses:
            if house['Hobby'] == 'gardening' and house['Birthday'] != 'april':
                return False
            if house['Birthday'] == 'april' and house['Hobby'] != 'gardening':
                return False
        
        # Constraint 9: jazz music and cooking hobby are the same house.
        for house in houses:
            if house['MusicGenre'] == 'jazz' and house['Hobby'] != 'cooking':
                return False
            if house['Hobby'] == 'cooking' and house['MusicGenre'] != 'jazz':
                return False
        
        # Constraint 10: rock music and mystery books are the same house.
        for house in houses:
            if house['MusicGenre'] == 'rock' and house['BookGenre'] != 'mystery':
                return False
            if house['BookGenre'] == 'mystery' and house['MusicGenre'] != 'rock':
                return False
        
        # Constraint 11: painting hobby is directly left of romance books.
        romance_index = None
        for i, house in enumerate(houses):
            if house['BookGenre'] == 'romance':
                romance_index = i
                break
        if romance_index is None or romance_index == 0:
            return False
        if houses[romance_index - 1]['Hobby'] != 'painting':
            return False
        
        # Constraint 12: Peter and pop music are the same house.
        for house in houses:
            if house['Name'] == 'Peter' and house['MusicGenre'] != 'pop':
                return False
            if house['MusicGenre'] == 'pop' and house['Name'] != 'Peter':
                return False
        
        # Constraint 13: gardening hobby and Arnold are the same house.
        for house in houses:
            if house['Hobby'] == 'gardening' and house['Name'] != 'Arnold':
                return False
            if house['Name'] == 'Arnold' and house['Hobby'] != 'gardening':
                return False
        
        # Constraint 14: rock music is directly left of jan birthday.
        jan_index = None
        for i, house in enumerate(houses):
            if house['Birthday'] == 'jan':
                jan_index = i
                break
        if jan_index is None or jan_index == 0:
            return False
        if houses[jan_index - 1]['MusicGenre'] != 'rock':
            return False
        
        # Constraint 16: cat animal is right of horse animal.
        horse_index = None
        cat_index = None
        for i, house in enumerate(houses):
            if house['Animal'] == 'horse':
                horse_index = i
            if house['Animal'] == 'cat':
                cat_index = i
        if horse_index is None or cat_index is None or cat_index <= horse_index:
            return False
        
        return True

    found_solution = None
    for names in itertools.permutations(attributes[0]):
        if names[1] == 'Eric':
            continue
        for hobbies in itertools.permutations(attributes[1]):
            if hobbies[2] == 'cooking':
                continue
            for animals in itertools.permutations(attributes[2]):
                for books in itertools.permutations(attributes[3]):
                    if books[3] == 'romance':
                        continue
                    for birthdays in itertools.permutations(attributes[4]):
                        for music in itertools.permutations(attributes[5]):
                            houses = []
                            for i in range(4):
                                house = {
                                    'Name': names[i],
                                    'Hobby': hobbies[i],
                                    'Animal': animals[i],
                                    'BookGenre': books[i],
                                    'Birthday': birthdays[i],
                                    'MusicGenre': music[i]
                                }
                                houses.append(house)
                            if check_constraints(houses):
                                found_solution = houses
                                break
                        if found_solution:
                            break
                    if found_solution:
                        break
                if found_solution:
                    break
            if found_solution:
                break
        if found_solution:
            break

    if found_solution is None:
        print("No solution found")
    else:
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": []
            }
        }
        for i, house in enumerate(found_solution):
            row = [str(i+1), house['Name'], house['Hobby'], house['Animal'], house['BookGenre'], house['Birthday'], house['MusicGenre']]
            solution_dict["solution"]["rows"].append(row)
        
        print(json.dumps(solution_dict, indent=2))

if __name__ == '__main__':
    main()