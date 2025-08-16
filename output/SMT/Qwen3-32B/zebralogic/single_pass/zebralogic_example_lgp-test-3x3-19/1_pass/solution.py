import json
from z3 import *

solver = Solver()

# Define EnumSorts
Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
Smoothie, (Desert, Watermelon, Cherry) = EnumSort('Smoothie', ['desert', 'watermelon', 'cherry'])
BookGenre, (SciFi, Romance, Mystery) = EnumSort('BookGenre', ['science fiction', 'romance', 'mystery'])

# Create variables for each house
house1_name = Const('house1_name', Name)
house1_smoothie = Const('house1_smoothie', Smoothie)
house1_book = Const('house1_book', BookGenre)

house2_name = Const('house2_name', Name)
house2_smoothie = Const('house2_smoothie', Smoothie)
house2_book = Const('house2_book', BookGenre)

house3_name = Const('house3_name', Name)
house3_smoothie = Const('house3_smoothie', Smoothie)
house3_book = Const('house3_book', BookGenre)

# Add distinctness constraints
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_smoothie, house2_smoothie, house3_smoothie))
solver.add(Distinct(house1_book, house2_book, house3_book))

# Clue 5: Peter is in the first house
solver.add(house1_name == Peter)

# Clue 2: Arnold loves mystery books
solver.add(
    Or(
        And(house2_name == Arnold, house2_book == Mystery),
        And(house3_name == Arnold, house3_book == Mystery)
    )
)

# Clue 4: Desert is directly left of Mystery
solver.add(
    Or(
        And(house1_smoothie == Desert, house2_book == Mystery),
        And(house2_smoothie == Desert, house3_book == Mystery)
    )
)

# Clue 1: Cherry is left of Mystery
solver.add(Implies(house2_smoothie == Cherry, house3_name == Arnold))
solver.add(house3_smoothie != Cherry)

# Clue 3: SciFi not in first house
solver.add(house1_book != SciFi)

if solver.check() == sat:
    model = solver.model()
    def get_str(var):
        return model.eval(var).as_string()
    
    rows = [
        ["1", get_str(house1_name), get_str(house1_smoothie), get_str(house1_book)],
        ["2", get_str(house2_name), get_str(house2_smoothie), get_str(house2_book)],
        ["3", get_str(house3_name), get_str(house3_smoothie), get_str(house3_book)]
    ]
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
    
else:
    print("No solution found.")