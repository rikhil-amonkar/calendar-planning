import itertools
import json

def solve():
    # Define all possible values for each attribute
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    birthdays = ["mar", "april", "sept", "feb", "jan"]
    mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    hair_colors = ["red", "blonde", "black", "gray", "brown"]
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all permutations of each attribute across 5 houses
    for name_perm in itertools.permutations(names, 5):
        for bday_perm in itertools.permutations(birthdays, 5):
            # Clue 1: March birthday in house 5
            if bday_perm[4] != "mar":
                continue
            # Clue 2: February birthday in house 1
            if bday_perm[0] != "feb":
                continue
            
            for mother_perm in itertools.permutations(mothers, 5):
                # Clue 4: Janelle in house 3
                if mother_perm[2] != "Janelle":
                    continue
                
                for occ_perm in itertools.permutations(occupations, 5):
                    # Clue 3: Eric is doctor
                    eric_index = name_perm.index("Eric")
                    if occ_perm[eric_index] != "doctor":
                        continue
                    
                    # Clue 6: artist in house 4
                    if occ_perm[3] != "artist":
                        continue
                    
                    # Clue 15: Peter is lawyer
                    peter_index = name_perm.index("Peter")
                    if occ_perm[peter_index] != "lawyer":
                        continue
                    
                    for hair_perm in itertools.permutations(hair_colors, 5):
                        # Clue 5: artist has brown hair
                        artist_index = occ_perm.index("artist")
                        if hair_perm[artist_index] != "brown":
                            continue
                        
                        # Clue 8: Peter has black hair
                        if hair_perm[peter_index] != "black":
                            continue
                        
                        # Clue 9: gray hair = teacher
                        teacher_index = occ_perm.index("teacher")
                        if hair_perm[teacher_index] != "gray":
                            continue
                        
                        # Clue 12: brown hair = jan birthday
                        brown_hair_index = hair_perm.index("brown")
                        if bday_perm[brown_hair_index] != "jan":
                            continue
                        
                        # Clue 13: Arnold has blonde hair
                        arnold_index = name_perm.index("Arnold")
                        if hair_perm[arnold_index] != "blonde":
                            continue
                        
                        # Clue 14: Holly mother = black hair
                        holly_mother_index = mother_perm.index("Holly")
                        if hair_perm[holly_mother_index] != "black":
                            continue
                        
                        # Clue 10: Alice's mother is Kailyn
                        alice_index = name_perm.index("Alice")
                        if mother_perm[alice_index] != "Kailyn":
                            continue
                        
                        # Clue 17: Alice has gray hair
                        if hair_perm[alice_index] != "gray":
                            continue
                        
                        # Clue 7: Penny is left of black hair
                        penny_index = mother_perm.index("Penny")
                        black_hair_index = hair_perm.index("black")
                        if not (penny_index < black_hair_index):
                            continue
                        
                        # Clue 11: Arnold is right of September birthday
                        sept_index = bday_perm.index("sept")
                        if not (arnold_index > sept_index):
                            continue
                        
                        # Clue 16: September birthday left of Kailyn mother
                        kailyn_index = mother_perm.index("Kailyn")
                        if not (sept_index < kailyn_index):
                            continue
                        
                        # All constraints satisfied - build solution
                        solution_rows = []
                        for i in range(5):
                            row = [
                                str(i + 1),
                                name_perm[i],
                                bday_perm[i],
                                mother_perm[i],
                                occ_perm[i],
                                hair_perm[i]
                            ]
                            solution_rows.append(row)
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                                "rows": solution_rows
                            }
                        }
                        return result
    
    return None

def main():
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()