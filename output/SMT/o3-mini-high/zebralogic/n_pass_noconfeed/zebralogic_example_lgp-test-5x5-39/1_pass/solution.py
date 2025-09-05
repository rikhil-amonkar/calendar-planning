from z3 import *
import json

def main():
    s = Solver()
    houses = 5

    # Create variables for each attribute in each house.
    names = [Int("name_%d" % i) for i in range(houses)]
    birthdays = [Int("bday_%d" % i) for i in range(houses)]
    mothers = [Int("mother_%d" % i) for i in range(houses)]
    occupations = [Int("occ_%d" % i) for i in range(houses)]
    haircolors = [Int("hair_%d" % i) for i in range(houses)]
    
    # Domain constraints: each variable is in {0,1,2,3,4}
    for group in [names, birthdays, mothers, occupations, haircolors]:
        for var in group:
            s.add(var >= 0, var < houses)
    
    # All different constraints for each category.
    s.add(Distinct(names))
    s.add(Distinct(birthdays))
    s.add(Distinct(mothers))
    s.add(Distinct(occupations))
    s.add(Distinct(haircolors))
    
    # Mappings (for our reference):
    # Names: 0: "Alice", 1: "Eric", 2: "Bob", 3: "Peter", 4: "Arnold"
    # Birthdays: 0: "mar", 1: "april", 2: "sept", 3: "feb", 4: "jan"
    # Mothers: 0: "Holly", 1: "Janelle", 2: "Kailyn", 3: "Penny", 4: "Aniya"
    # Occupations: 0: "engineer", 1: "doctor", 2: "lawyer", 3: "artist", 4: "teacher"
    # HairColors: 0: "red", 1: "blonde", 2: "black", 3: "gray", 4: "brown"
    
    # Clue 1: The person whose birthday is in March is in the fifth house.
    # "mar" is mapped to 0; house index 4 must have birthday 0.
    s.add(birthdays[4] == 0)
    
    # Clue 2: The person whose birthday is in February is in the first house.
    # "feb" is mapped to 3; house index 0 must have birthday 3.
    s.add(birthdays[0] == 3)
    
    # Clue 3: The person who is a doctor is Eric.
    # Eric is 1 and doctor is 1; enforce bi-implication.
    for i in range(houses):
        s.add(Implies(names[i] == 1, occupations[i] == 1))
        s.add(Implies(occupations[i] == 1, names[i] == 1))
    
    # Clue 4: The person whose mother's name is Janelle is in the third house.
    # Janelle is 1; thus in house index 2, mother must equal 1.
    s.add(mothers[2] == 1)
    
    # Clue 6: The person who is an artist is in the fourth house.
    # Artist is 3; so house index 3 occupation is 3.
    s.add(occupations[3] == 3)
    
    # Clue 5: The person who is an artist is the person who has brown hair.
    # Brown hair is 4.
    for i in range(houses):
        s.add(Implies(occupations[i] == 3, haircolors[i] == 4))
        s.add(Implies(haircolors[i] == 4, occupations[i] == 3))
    
    # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    # Penny is 3 and black hair is 2. Use the indices to enforce ordering.
    black_house = Sum([If(haircolors[i] == 2, i, 0) for i in range(houses)])
    penny_house = Sum([If(mothers[i] == 3, i, 0) for i in range(houses)])
    s.add(penny_house < black_house)
    
    # Clue 8: Peter is the person who has black hair.
    # Peter is 3, black hair is 2.
    for i in range(houses):
        s.add(Implies(names[i] == 3, haircolors[i] == 2))
    
    # Clue 14: The person whose mother's name is Holly is the person who has black hair.
    # Holly is 0.
    for i in range(houses):
        s.add(Implies(mothers[i] == 0, haircolors[i] == 2))
        s.add(Implies(haircolors[i] == 2, mothers[i] == 0))
    
    # Clue 9: The person who has gray hair is the person who is a teacher.
    # Gray is 3, teacher is 4.
    for i in range(houses):
        s.add(Implies(haircolors[i] == 3, occupations[i] == 4))
        s.add(Implies(occupations[i] == 4, haircolors[i] == 3))
    
    # Clue 10: Alice is the person whose mother's name is Kailyn.
    # Alice is 0; Kailyn is 2.
    for i in range(houses):
        s.add(Implies(names[i] == 0, mothers[i] == 2))
    
    # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
    # Arnold is 4; September is 2.
    sept_house = Sum([If(birthdays[i] == 2, i, 0) for i in range(houses)])
    arnold_house = Sum([If(names[i] == 4, i, 0) for i in range(houses)])
    s.add(sept_house < arnold_house)
    
    # Clue 12: The person who has brown hair is the person whose birthday is in January.
    # Brown hair is 4; January is 4.
    for i in range(houses):
        s.add(Implies(haircolors[i] == 4, birthdays[i] == 4))
        s.add(Implies(birthdays[i] == 4, haircolors[i] == 4))
    
    # Clue 13: Arnold is the person who has blonde hair.
    # Arnold is 4; blonde is 1.
    for i in range(houses):
        s.add(Implies(names[i] == 4, haircolors[i] == 1))
    
    # Clue 15: Peter is the person who is a lawyer.
    # Peter is 3; lawyer is 2.
    for i in range(houses):
        s.add(Implies(names[i] == 3, occupations[i] == 2))
    
    # Clue 16: The person whose birthday is in September is somewhere to the left of the person whose mother's name is Kailyn.
    # September is 2; Kailyn is 2.
    kailyn_house = Sum([If(mothers[i] == 2, i, 0) for i in range(houses)])
    s.add(sept_house < kailyn_house)
    
    # Clue 17: Alice is the person who has gray hair.
    # Alice is 0; gray is 3.
    for i in range(houses):
        s.add(Implies(names[i] == 0, haircolors[i] == 3))
    
    # Solve the puzzle
    if s.check() == sat:
        m = s.model()
        # Reverse mapping dictionaries for output.
        names_map = {0: "Alice", 1: "Eric", 2: "Bob", 3: "Peter", 4: "Arnold"}
        birthday_map = {0: "mar", 1: "april", 2: "sept", 3: "feb", 4: "jan"}
        mothers_map = {0: "Holly", 1: "Janelle", 2: "Kailyn", 3: "Penny", 4: "Aniya"}
        occupations_map = {0: "engineer", 1: "doctor", 2: "lawyer", 3: "artist", 4: "teacher"}
        hair_map = {0: "red", 1: "blonde", 2: "black", 3: "gray", 4: "brown"}
        
        solution_rows = []
        for i in range(houses):
            house_number = str(i + 1)
            name_val = m[names[i]].as_long()
            bday_val = m[birthdays[i]].as_long()
            mother_val = m[mothers[i]].as_long()
            occ_val = m[occupations[i]].as_long()
            hair_val = m[haircolors[i]].as_long()
            row = [
                house_number,
                names_map[name_val],
                birthday_map[bday_val],
                mothers_map[mother_val],
                occupations_map[occ_val],
                hair_map[hair_val]
            ]
            solution_rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": {}}))
        
if __name__ == "__main__":
    main()