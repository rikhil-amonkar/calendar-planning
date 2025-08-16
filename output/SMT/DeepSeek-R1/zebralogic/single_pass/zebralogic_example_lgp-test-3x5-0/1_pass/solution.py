import z3
import json

def main():
    # Define the enums for each attribute
    NameSort, (Peter, Arnold, Eric) = z3.EnumSort('Name', ['Peter', 'Arnold', 'Eric'])
    BookGenreSort, (ScienceFiction, Mystery, Romance) = z3.EnumSort('BookGenre', ['science fiction', 'mystery', 'romance'])
    SmoothieSort, (Watermelon, Desert, Cherry) = z3.EnumSort('Smoothie', ['watermelon', 'desert', 'cherry'])
    BirthdaySort, (April, Jan, Sept) = z3.EnumSort('Birthday', ['april', 'jan', 'sept'])
    HeightSort, (Average, VeryShort, Short) = z3.EnumSort('Height', ['average', 'very short', 'short'])
    
    # Create dictionaries to map constants to strings
    name_map = { Peter: "Peter", Arnold: "Arnold", Eric: "Eric" }
    book_genre_map = { ScienceFiction: "science fiction", Mystery: "mystery", Romance: "romance" }
    smoothie_map = { Watermelon: "watermelon", Desert: "desert", Cherry: "cherry" }
    birthday_map = { April: "april", Jan: "jan", Sept: "sept" }
    height_map = { Average: "average", VeryShort: "very short", Short: "short" }
    
    # Create variables for each house (0,1,2 for houses 1,2,3)
    names = [z3.Const('name_%d' % i, NameSort) for i in range(3)]
    book_genres = [z3.Const('book_genre_%d' % i, BookGenreSort) for i in range(3)]
    smoothies = [z3.Const('smoothie_%d' % i, SmoothieSort) for i in range(3)]
    birthdays = [z3.Const('birthday_%d' % i, BirthdaySort) for i in range(3)]
    heights = [z3.Const('height_%d' % i, HeightSort) for i in range(3)]
    
    s = z3.Solver()
    
    # Add distinct constraints for each attribute
    s.add(z3.Distinct(names))
    s.add(z3.Distinct(book_genres))
    s.add(z3.Distinct(smoothies))
    s.add(z3.Distinct(birthdays))
    s.add(z3.Distinct(heights))
    
    # Clue 1: The person who likes Cherry smoothies is not in the second house.
    s.add(smoothies[1] != Cherry)
    
    # Clue 2: Arnold is the person who loves mystery books.
    for i in range(3):
        s.add(z3.Implies(names[i] == Arnold, book_genres[i] == Mystery))
    
    # Clue 3: The person whose birthday is in January is not in the first house.
    s.add(birthdays[0] != Jan)
    
    # Clue 4: The person who is very short is the person who loves romance books.
    for i in range(3):
        s.add((heights[i] == VeryShort) == (book_genres[i] == Romance))
    
    # Clue 5: The person who loves mystery books is the person whose birthday is in September.
    for i in range(3):
        s.add((book_genres[i] == Mystery) == (birthdays[i] == Sept))
    
    # Clue 6: The person who has an average height is the Desert smoothie lover.
    for i in range(3):
        s.add((heights[i] == Average) == (smoothies[i] == Desert))
    
    # Clue 7: Eric is in the first house.
    s.add(names[0] == Eric)
    
    # Clue 8: The Watermelon smoothie lover is the person who is short.
    for i in range(3):
        s.add((smoothies[i] == Watermelon) == (heights[i] == Short))
    
    # Clue 9: The Watermelon smoothie lover is Eric.
    for i in range(3):
        s.add((smoothies[i] == Watermelon) == (names[i] == Eric))
    
    if s.check() == z3.sat:
        m = s.model()
        rows = []
        for i in range(3):
            house_num = str(i+1)
            n_val = m[names[i]]
            name_str = name_map[n_val]
            
            bg_val = m[book_genres[i]]
            bg_str = book_genre_map[bg_val]
            
            sm_val = m[smoothies[i]]
            sm_str = smoothie_map[sm_val]
            
            bd_val = m[birthdays[i]]
            bd_str = birthday_map[bd_val]
            
            h_val = m[heights[i]]
            h_str = height_map[h_val]
            
            row = [house_num, name_str, bg_str, sm_str, bd_str, h_str]
            rows.append(row)
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()