from z3 import *

def main():
    # Define the enums and constants for each attribute
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    BookGenre, (SciFi, Mystery) = EnumSort('BookGenre', ['science fiction', 'mystery'])
    Birthday, (April, Sept) = EnumSort('Birthday', ['april', 'sept'])
    Animal, (Horse, Cat) = EnumSort('Animal', ['horse', 'cat'])
    
    # Create variables for house 1
    n1 = Const('n1', Name)
    b1 = Const('b1', BookGenre)
    d1 = Const('d1', Birthday)
    a1 = Const('a1', Animal)
    
    # Create variables for house 2
    n2 = Const('n2', Name)
    b2 = Const('b2', BookGenre)
    d2 = Const('d2', Birthday)
    a2 = Const('a2', Animal)
    
    s = Solver()
    
    # Each attribute must be unique across the two houses
    s.add(Distinct(n1, n2))
    s.add(Distinct(b1, b2))
    s.add(Distinct(d1, d2))
    s.add(Distinct(a1, a2))
    
    # Clue 1: Eric is in the first house.
    s.add(n1 == Eric)
    
    # Clue 2: Eric is the person whose birthday is in September.
    s.add(d1 == Sept)  # Since Eric is in house1, house1 has Sept birthday.
    
    # Clue 3: The person who loves science fiction books is in the second house.
    s.add(b2 == SciFi)
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September.
    s.add(a1 == Horse)  # Since house1 has Sept birthday, house1 has horse.
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        
        # Map the Z3 constants back to their string representations
        name_map = {Eric: "Eric", Arnold: "Arnold"}
        book_map = {SciFi: "science fiction", Mystery: "mystery"}
        birthday_map = {April: "april", Sept: "sept"}
        animal_map = {Horse: "horse", Cat: "cat"}
        
        # Retrieve the values for house 1
        house1_name = name_map[m[n1]]
        house1_book = book_map[m[b1]]
        house1_bday = birthday_map[m[d1]]
        house1_animal = animal_map[m[a1]]
        
        # Retrieve the values for house 2
        house2_name = name_map[m[n2]]
        house2_book = book_map[m[b2]]
        house2_bday = birthday_map[m[d2]]
        house2_animal = animal_map[m[a2]]
        
        # Construct the rows for the output
        rows = [
            ["1", house1_name, house1_book, house1_bday, house1_animal],
            ["2", house2_name, house2_book, house2_bday, house2_animal]
        ]
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                "rows": rows
            }
        }
        
        # Output as JSON string (though the problem expects the code to print the dictionary, but note: the problem says "output must be valid JSON")
        # However, the problem requires the code to be in a Python block that prints the solution when run.
        # We'll print the dictionary in a way that it's a valid JSON string? But the problem says "Your output should be a JSON-formatted dictionary"
        # Actually, the problem says: "Write a Python program that solves it using the Z3 solver." and output the code.
        # But when run, the program should output the JSON. However, the problem expects the code to be surrounded by