import json
from z3 import *

def main():
    # Define the sorts and constants for each attribute
    Name, (Alice, Eric, Bob, Peter, Arnold) = EnumSort('Name', ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold'])
    Birthday, (jan, feb, mar, april, sept) = EnumSort('Birthday', ['jan', 'feb', 'mar', 'april', 'sept'])
    Mother, (Holly, Janelle, Kailyn, Penny, Aniya) = EnumSort('Mother', ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya'])
    Occupation, (engineer, doctor, lawyer, artist, teacher) = EnumSort('Occupation', ['engineer', 'doctor', 'lawyer', 'artist', 'teacher'])
    HairColor, (red, blonde, black, gray, brown) = EnumSort('HairColor', ['red', 'blonde', 'black', 'gray', 'brown'])

    # Create lists for each attribute per house (index 0 to 4 represent houses 1 to 5)
    names = [Const('name_%d' % i, Name) for i in range(5)]
    birthdays = [Const('birthday_%d' % i, Birthday) for i in range(5)]
    mothers = [Const('mother_%d' % i, Mother) for i in range(5)]
    occupations = [Const('occupation_%d' % i, Occupation) for i in range(5)]
    hair_colors = [Const('hair_color_%d' % i, HairColor) for i in range(5)]

    s = Solver()

    # Each attribute must have distinct values across houses
    s.add(Distinct(names))
    s.add(Distinct(birthdays))
    s.add(Distinct(mothers))
    s.add(Distinct(occupations))
    s.add(Distinct(hair_colors))

    # Add constraints from clues
    s.add(birthdays[4] == mar)  # Clue 1: March birthday in house 5
    s.add(birthdays[0] == feb)   # Clue 2: February birthday in house 1
    # Clue 3: Doctor is Eric
    s.add(Or([And(occupations[i] == doctor, names[i] == Eric) for i in range(5)]))
    s.add(mothers[2] == Janelle)  # Clue 4: Janelle mother in house 3
    # Clue 5: Artist has brown hair
    s.add(Or([And(occupations[i] == artist, hair_colors[i] == brown) for i in range(5)]))
    s.add(occupations[3] == artist)  # Clue 6: Artist in house 4
    # Clue 7: Penny mother left of black hair
    s.add(Or([And(mothers[i] == Penny, Or([And(hair_colors[j] == black, i < j) for j in range(i+1, 5)])) for i in range(4)]))
    # Clue 8: Peter has black hair
    s.add(Or([And(names[i] == Peter, hair_colors[i] == black) for i in range(5)]))
    # Clue 9: Gray hair is teacher
    s.add(Or([And(hair_colors[i] == gray, occupations[i] == teacher) for i in range(5)]))
    # Clue 10: Alice has mother Kailyn
    s.add(Or([And(names[i] == Alice, mothers[i] == Kailyn) for i in range(5)]))
    # Clue 11: Arnold right of September birthday
    s.add(Or([And(birthdays[i] == sept, names[j] == Arnold, i < j) for j in range(1,5) for i in range(j)]))
    # Clue 12: Brown hair has January birthday
    s.add(Or([And(hair_colors[i] == brown, birthdays[i] == jan) for i in range(5)]))
    # Clue 13: Arnold has blonde hair
    s.add(Or([And(names[i] == Arnold, hair_colors[i] == blonde) for i in range(5)]))
    # Clue 14: Holly mother has black hair
    s.add(Or([And(mothers[i] == Holly, hair_colors[i] == black) for i in range(5)]))
    # Clue 15: Peter is lawyer
    s.add(Or([And(names[i] == Peter, occupations[i] == lawyer) for i in range(5)]))
    # Clue 16: September birthday left of Kailyn mother
    s.add(Or([And(birthdays[i] == sept, mothers[j] == Kailyn, i < j) for j in range(1,5) for i in range(j)]))
    # Clue 17: Alice has gray hair
    s.add(Or([And(names[i] == Alice, hair_colors[i] == gray) for i in range(5)]))
    
    # Deduced from clues 5, 6, and 12: House 4 has artist, brown hair, and January birthday
    s.add(hair_colors[3] == brown)
    s.add(birthdays[3] == jan)

    if s.check() == sat:
        m = s.model()
        
        # Constants to string mappings
        name_consts = [Alice, Eric, Bob, Peter, Arnold]
        name_strs = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
        
        birthday_consts = [jan, feb, mar, april, sept]
        birthday_strs = ['jan', 'feb', 'mar', 'april', 'sept']
        
        mother_consts = [Holly, Janelle, Kailyn, Penny, Aniya]
        mother_strs = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
        
        occupation_consts = [engineer, doctor, lawyer, artist, teacher]
        occupation_strs = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
        
        hair_color_consts = [red, blonde, black, gray, brown]
        hair_color_strs = ['red', 'blonde', 'black', 'gray', 'brown']
        
        def get_str_value(z3_val, const_list, str_list):
            for i, c in enumerate(const_list):
                if m.eq(z3_val, c):
                    return str_list[i]
            return None
        
        rows = []
        for i in range(5):
            n_val = get_str_value(names[i], name_consts, name_strs)
            b_val = get_str_value(birthdays[i], birthday_consts, birthday_strs)
            m_val = get_str_value(mothers[i], mother_consts, mother_strs)
            o_val = get_str_value(occupations[i], occupation_consts, occupation_strs)
            h_val = get_str_value(hair_colors[i], hair_color_consts, hair_color_strs)
            rows.append([str(i+1), n_val, b_val, m_val, o_val, h_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()