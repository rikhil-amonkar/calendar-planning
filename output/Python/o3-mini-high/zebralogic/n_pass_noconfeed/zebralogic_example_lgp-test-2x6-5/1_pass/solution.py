import json
import itertools

def solve_puzzle():
    # Define possible values for each attribute.
    houses = [1, 2]  # House numbers as positions (left-to-right)
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    solutions = []
    
    # Generate all possible assignments using permutations for each attribute.
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for bday_perm in itertools.permutations(birthdays):
                for style_perm in itertools.permutations(house_styles):
                    for height_perm in itertools.permutations(heights):
                        for cigar_perm in itertools.permutations(cigars):
                            # Construct an assignment for the 2 houses.
                            assignment = []
                            for i in range(2):
                                house = {
                                    "House": str(houses[i]),
                                    "Name": name_perm[i],
                                    "Occupation": occ_perm[i],
                                    "Birthday": bday_perm[i],
                                    "HouseStyle": style_perm[i],
                                    "Height": height_perm[i],
                                    "Cigar": cigar_perm[i]
                                }
                                assignment.append(house)
                            
                            # Constraint 1: The engineer is in the first house.
                            if assignment[0]["Occupation"] != "engineer":
                                continue
                            
                            # Constraint 6: The engineer is Eric.
                            engineer_house = None
                            for h in assignment:
                                if h["Occupation"] == "engineer":
                                    engineer_house = h
                                    break
                            if engineer_house is None or engineer_house["Name"] != "Eric":
                                continue
                            
                            # Constraint 3: The person living in a colonial-style house is the engineer.
                            valid = True
                            for h in assignment:
                                if h["HouseStyle"] == "colonial" and h["Occupation"] != "engineer":
                                    valid = False
                                    break
                                if h["Occupation"] == "engineer" and h["HouseStyle"] != "colonial":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 4: The person who is very short is the engineer.
                            valid = True
                            for h in assignment:
                                if h["Height"] == "very short" and h["Occupation"] != "engineer":
                                    valid = False
                                    break
                                if h["Occupation"] == "engineer" and h["Height"] != "very short":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 5: The person who is short is partial to Pall Mall.
                            valid = True
                            for h in assignment:
                                if h["Height"] == "short" and h["Cigar"] != "pall mall":
                                    valid = False
                                    break
                                if h["Cigar"] == "pall mall" and h["Height"] != "short":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 2: The person whose birthday is in April and the doctor are next to each other.
                            idx_april = None
                            idx_doctor = None
                            for i, h in enumerate(assignment):
                                if h["Birthday"] == "april":
                                    idx_april = i
                                if h["Occupation"] == "doctor":
                                    idx_doctor = i
                            if idx_april is None or idx_doctor is None or abs(idx_april - idx_doctor) != 1:
                                continue
                            
                            # All constraints satisfied; add the solution.
                            solutions.append(assignment)
                            
    return solutions

def main():
    sols = solve_puzzle()
    # Prepare the JSON output with the specified format.
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    solution_rows = []
    
    if sols:
        # Use the first valid solution and order houses as per the puzzle (house 1, then house 2).
        for house in sols[0]:
            row = [house[attr] for attr in header]
            solution_rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": solution_rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()