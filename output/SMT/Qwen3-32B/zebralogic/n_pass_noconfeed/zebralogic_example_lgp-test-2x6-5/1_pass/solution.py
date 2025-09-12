from z3 import *

def main():
    # Define EnumSorts and their constants
    name_enum, (arnold, eric) = EnumSort('Name', ['Arnold', 'Eric'])
    occupation_enum, (engineer, doctor) = EnumSort('Occupation', ['engineer', 'doctor'])
    birthday_enum, (april, sept) = EnumSort('Birthday', ['april', 'sept'])
    housestyle_enum, (victorian, colonial) = EnumSort('HouseStyle', ['victorian', 'colonial'])
    height_enum, (very_short, short) = EnumSort('Height', ['very short', 'short'])
    cigar_enum, (pall_mall, prince) = EnumSort('Cigar', ['pall mall', 'prince'])

    # Create variables for each house's attributes
    name1, name2 = Consts('name1 name2', name_enum)
    occupation1, occupation2 = Consts('occupation1 occupation2', occupation_enum)
    birthday1, birthday2 = Consts('birthday1 birthday2', birthday_enum)
    housestyle1, housestyle2 = Consts('housestyle1 housestyle2', housestyle_enum)
    height1, height2 = Consts('height1 height2', height_enum)
    cigar1, cigar2 = Consts('cigar1 cigar2', cigar_enum)

    s = Solver()

    # Uniqueness constraints
    s.add(name1 != name2)
    s.add(occupation1 != occupation2)
    s.add(birthday1 != birthday2)
    s.add(housestyle1 != housestyle2)
    s.add(height1 != height2)
    s.add(cigar1 != cigar2)

    # Clue 1: Engineer in first house
    s.add(occupation1 == engineer)

    # Clue 6: Engineer is Eric
    s.add(name1 == eric)

    # Clue 3: Colonial-style is engineer's house (house1)
    s.add(housestyle1 == colonial)

    # Clue 4: Engineer (house1) is very short
    s.add(height1 == very_short)

    # Clue 5: Short person likes Pall Mall
    s.add(Implies(height1 == short, cigar1 == pall_mall))
    s.add(Implies(height2 == short, cigar2 == pall_mall))

    # Clue 2: April and doctor are adjacent
    s.add(Or(
        And(birthday1 == april, occupation2 == doctor),
        And(birthday2 == april, occupation1 == doctor)
    ))

    # Check satisfiability
    if s.check() == sat:
        model = s.model()

        # Extract values for each house
        row1 = [
            "1",
            model[name1],
            model[occupation1],
            model[birthday1],
            model[housestyle1],
            model[height1],
            model[cigar1],
        ]
        row2 = [
            "2",
            model[name2],
            model[occupation2],
            model[birthday2],
            model[housestyle2],
            model[height2],
            model[cigar2],
        ]

        # Convert from Z3 expressions to strings
        row1 = ["1"] + [str(val) for val in row1[1:]]
        row2 = ["2"] + [str(val) for val in row2[1:]]

        # Prepare JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": [row1, row2]
            }
        }

        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()