from z3 import *
import json

# Create solver
s = Solver()

# Variables for house 1
is_arnold_1 = Bool('is_arnold_1')
is_engineer_1 = Bool('is_engineer_1')
is_april_1 = Bool('is_april_1')
is_victorian_1 = Bool('is_victorian_1')
is_very_short_1 = Bool('is_very_short_1')
is_pall_mall_1 = Bool('is_pall_mall_1')

# Variables for house 2
is_arnold_2 = Bool('is_arnold_2')
is_engineer_2 = Bool('is_engineer_2')
is_april_2 = Bool('is_april_2')
is_victorian_2 = Bool('is_victorian_2')
is_very_short_2 = Bool('is_very_short_2')
is_pall_mall_2 = Bool('is_pall_mall_2')

# Add constraints for uniqueness per attribute
# Names
s.add(Or(is_arnold_1, is_arnold_2))
s.add(Not(And(is_arnold_1, is_arnold_2)))

# Occupations
s.add(Or(is_engineer_1, is_engineer_2))
s.add(Not(And(is_engineer_1, is_engineer_2)))

# Birthdays
s.add(Or(is_april_1, is_april_2))
s.add(Not(And(is_april_1, is_april_2)))

# HouseStyles
s.add(Or(is_victorian_1, is_victorian_2))
s.add(Not(And(is_victorian_1, is_victorian_2)))

# Heights
s.add(Or(is_very_short_1, is_very_short_2))
s.add(Not(And(is_very_short_1, is_very_short_2)))

# Cigars
s.add(Or(is_pall_mall_1, is_pall_mall_2))
s.add(Not(And(is_pall_mall_1, is_pall_mall_2)))

# Add clues
# Clue 1: Engineer in first house
s.add(is_engineer_1)

# Clue 3: Colonial-style is engineer's house (house 1)
s.add(Not(is_victorian_1))

# Clue 4: Engineer (house 1) is very short
s.add(is_very_short_1)

# Clue 5: Short person (house 2) likes Pall Mall
s.add(Not(is_very_short_2))
s.add(is_pall_mall_2)

# Clue 6: Engineer is Eric (house 1's name is Eric)
s.add(Not(is_arnold_1))

# Clue 2: April and doctor are next to each other (doctor is in house 2, so April is in house 1)
s.add(is_april_1)

if s.check() == sat:
    model = s.model()
    
    def get_bool(var):
        return model.eval(var).as_bool()
    
    # House 1 values
    h1_arnold = get_bool(is_arnold_1)
    h1_engineer = get_bool(is_engineer_1)
    h1_april = get_bool(is_april_1)
    h1_victorian = get_bool(is_victorian_1)
    h1_very_short = get_bool(is_very_short_1)
    h1_pall_mall = get_bool(is_pall_mall_1)
    
    # House 2 values
    h2_arnold = get_bool(is_arnold_2)
    h2_engineer = get_bool(is_engineer_2)
    h2_april = get_bool(is_april_2)
    h2_victorian = get_bool(is_victorian_2)
    h2_very_short = get_bool(is_very_short_2)
    h2_pall_mall = get_bool(is_pall_mall_2)
    
    # Determine each attribute for both houses
    name_1 = 'Arnold' if h1_arnold else 'Eric'
    name_2 = 'Arnold' if h2_arnold else 'Eric'
    
    occupation_1 = 'engineer' if h1_engineer else 'doctor'
    occupation_2 = 'engineer' if h2_engineer else 'doctor'
    
    birthday_1 = 'april' if h1_april else 'sept'
    birthday_2 = 'april' if h2_april else 'sept'
    
    housestyle_1 = 'victorian' if h1_victorian else 'colonial'
    housestyle_2 = 'victorian' if h2_victorian else 'colonial'
    
    height_1 = 'very short' if h1_very_short else 'short'
    height_2 = 'very short' if h2_very_short else 'short'
    
    cigar_1 = 'pall mall' if h1_pall_mall else 'prince'
    cigar_2 = 'pall mall' if h2_pall_mall else 'prince'
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": [
                ["1", name_1, occupation_1, birthday_1, housestyle_1, height_1, cigar_1],
                ["2", name_2, occupation_2, birthday_2, housestyle_2, height_2, cigar_2]
            ]
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")