import json

def main():
    names = ['Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery']
    vacations = ['mountain', 'beach']
    animals = ['cat', 'horse']
    music_genres = ['rock', 'pop']
    
    def check_constraints(house1, house2):
        houses = [house1, house2]
        
        # Constraint 1: Beach vacation is Eric
        beach_house = None
        for house in houses:
            if house['Vacation'] == 'beach':
                beach_house = house
        if beach_house is None or beach_house['Name'] != 'Eric':
            return False
        
        # Constraint 2: Pop music is the same as beach vacation
        pop_house = None
        for house in houses:
            if house['MusicGenre'] == 'pop':
                pop_house = house
        if pop_house is None or pop_house != beach_house:
            return False
        
        # Constraint 3: Rock music is the same as mystery books
        rock_house = None
        mystery_house = None
        for house in houses:
            if house['MusicGenre'] == 'rock':
                rock_house = house
            if house['BookGenre'] == 'mystery':
                mystery_house = house
        if rock_house is None or mystery_house is None or rock_house != mystery_house:
            return False
        
        # Constraint 4: Cat lover is in house 1
        cat_house = None
        for house in houses:
            if house['Animal'] == 'cat':
                cat_house = house
        if cat_house is None or cat_house['House'] != '1':
            return False
        
        # Constraint 5: Mystery books in house 1
        if mystery_house['House'] != '1':
            return False
        
        return True

    solutions = []
    for n1 in names:
        n2 = next(n for n in names if n != n1)
        for b1 in book_genres:
            b2 = next(b for b in book_genres if b != b1)
            for v1 in vacations:
                v2 = next(v for v in vacations if v != v1)
                for a1 in animals:
                    a2 = next(a for a in animals if a != a1)
                    for m1 in music_genres:
                        m2 = next(m for m in music_genres if m != m1)
                        
                        house1 = {
                            'House': '1',
                            'Name': n1,
                            'BookGenre': b1,
                            'Vacation': v1,
                            'Animal': a1,
                            'MusicGenre': m1
                        }
                        house2 = {
                            'House': '2',
                            'Name': n2,
                            'BookGenre': b2,
                            'Vacation': v2,
                            'Animal': a2,
                            'MusicGenre': m2
                        }
                        
                        if check_constraints(house1, house2):
                            solutions.append((house1, house2))
    
    if solutions:
        house1, house2 = solutions[0]
        row1 = [house1['House'], house1['Name'], house1['BookGenre'], house1['Vacation'], house1['Animal'], house1['MusicGenre']]
        row2 = [house2['House'], house2['Name'], house2['BookGenre'], house2['Vacation'], house2['Animal'], house2['MusicGenre']]
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": [row1, row2]
            }
        }
    else:
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": []
            }
        }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()