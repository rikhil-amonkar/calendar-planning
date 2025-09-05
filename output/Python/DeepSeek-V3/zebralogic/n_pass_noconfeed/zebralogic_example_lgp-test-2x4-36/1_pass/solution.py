import json

def main():
    # Define the attributes
    names = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']
    birthday_months = ['april', 'sept']
    animals = ['horse', 'cat']
    
    houses = [1, 2]
    
    # Initialize all possibilities
    possibilities = []
    for house in houses:
        for name in names:
            for book_genre in book_genres:
                for birthday in birthday_months:
                    for animal in animals:
                        possibilities.append({
                            'house': house,
                            'name': name,
                            'book_genre': book_genre,
                            'birthday': birthday,
                            'animal': animal
                        })
    
    # Apply constraints
    # Clue 1: Eric is in the first house.
    possibilities = [p for p in possibilities if not (p['house'] == 1 and p['name'] != 'Eric')]
    possibilities = [p for p in possibilities if not (p['name'] == 'Eric' and p['house'] != 1)]
    
    # Clue 2: Eric is the person whose birthday is in September.
    possibilities = [p for p in possibilities if not (p['name'] == 'Eric' and p['birthday'] != 'sept')]
    possibilities = [p for p in possibilities if not (p['birthday'] == 'sept' and p['name'] != 'Eric')]
    
    # Clue 3: The person who loves science fiction books is in the second house.
    possibilities = [p for p in possibilities if not (p['book_genre'] == 'science fiction' and p['house'] != 2)]
    possibilities = [p for p in possibilities if not (p['house'] == 2 and p['book_genre'] != 'science fiction')]
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September.
    possibilities = [p for p in possibilities if not (p['animal'] == 'horse' and p['birthday'] != 'sept')]
    possibilities = [p for p in possibilities if not (p['birthday'] == 'sept' and p['animal'] != 'horse')]
    
    # Group by house and ensure unique attributes
    house1 = [p for p in possibilities if p['house'] == 1]
    house2 = [p for p in possibilities if p['house'] == 2]
    
    # Since all constraints are applied, we should have exactly one possibility per house
    if len(house1) == 1 and len(house2) == 1:
        solution_house1 = house1[0]
        solution_house2 = house2[0]
        
        # Build the output
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                "rows": [
                    ["1", solution_house1['name'], solution_house1['book_genre'], solution_house1['birthday'], solution_house1['animal']],
                    ["2", solution_house2['name'], solution_house2['book_genre'], solution_house2['birthday'], solution_house2['animal']]
                ]
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print("Error: Could not find a unique solution")

if __name__ == "__main__":
    main()