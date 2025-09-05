import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    book_perms = list(permutations(book_genres))
    smoothie_perms = list(permutations(smoothies))
    birthday_perms = list(permutations(birthdays))
    height_perms = list(permutations(heights))
    
    # Try all combinations
    for name_assignment in name_perms:
        for book_assignment in book_perms:
            for smoothie_assignment in smoothie_perms:
                for birthday_assignment in birthday_perms:
                    for height_assignment in height_perms:
                        # Create a solution candidate
                        candidate = []
                        for i in range(3):
                            house = i + 1
                            candidate.append({
                                'house': house,
                                'name': name_assignment[i],
                                'book': book_assignment[i],
                                'smoothie': smoothie_assignment[i],
                                'birthday': birthday_assignment[i],
                                'height': height_assignment[i]
                            })
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The person who likes Cherry smoothies is not in the second house.
                        for house in candidate:
                            if house['smoothie'] == 'cherry' and house['house'] == 2:
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 2: Arnold is the person who loves mystery books.
                        for house in candidate:
                            if house['name'] == 'Arnold' and house['book'] != 'mystery':
                                valid = False
                                break
                            if house['book'] == 'mystery' and house['name'] != 'Arnold':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 3: The person whose birthday is in January is not in the first house.
                        for house in candidate:
                            if house['birthday'] == 'jan' and house['house'] == 1:
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 4: The person who is very short is the person who loves romance books.
                        for house in candidate:
                            if house['height'] == 'very short' and house['book'] != 'romance':
                                valid = False
                                break
                            if house['book'] == 'romance' and house['height'] != 'very short':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 5: The person who loves mystery books is the person whose birthday is in September.
                        for house in candidate:
                            if house['book'] == 'mystery' and house['birthday'] != 'sept':
                                valid = False
                                break
                            if house['birthday'] == 'sept' and house['book'] != 'mystery':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 6: The person who has an average height is the Desert smoothie lover.
                        for house in candidate:
                            if house['height'] == 'average' and house['smoothie'] != 'desert':
                                valid = False
                                break
                            if house['smoothie'] == 'desert' and house['height'] != 'average':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 7: Eric is in the first house.
                        if candidate[0]['name'] != 'Eric':
                            valid = False
                            continue
                            
                        # Clue 8: The Watermelon smoothie lover is the person who is short.
                        for house in candidate:
                            if house['smoothie'] == 'watermelon' and house['height'] != 'short':
                                valid = False
                                break
                            if house['height'] == 'short' and house['smoothie'] != 'watermelon':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Clue 9: The Watermelon smoothie lover is Eric.
                        for house in candidate:
                            if house['smoothie'] == 'watermelon' and house['name'] != 'Eric':
                                valid = False
                                break
                            if house['name'] == 'Eric' and house['smoothie'] != 'watermelon':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If we get here, we found a valid solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                "rows": []
                            }
                        }
                        
                        # Sort by house number and format the solution
                        candidate.sort(key=lambda x: x['house'])
                        for house in candidate:
                            solution["solution"]["rows"].append([
                                str(house['house']),
                                house['name'],
                                house['book'],
                                house['smoothie'],
                                house['birthday'],
                                house['height']
                            ])
                        
                        print(json.dumps(solution, indent=2))
                        return
    
    print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()