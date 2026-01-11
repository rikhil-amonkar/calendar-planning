import json
from itertools import permutations

def solve():
    # Define all possible values
    names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors = ["blue", "green", "white", "yellow", "red"]
    phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]
    houses = [1, 2, 3, 4, 5]
    
    # We'll generate all permutations and filter by constraints
    # Since 5!^4 is huge, we'll use a backtracking search with pruning
    
    # Helper function to check if assignment is consistent
    def check_constraints(assignment):
        # assignment is a list of tuples (house, name, color, phone, occupation)
        # indexed by house-1
        
        # Build maps for quick lookup
        by_house = {h: (name, color, phone, occ) for h, name, color, phone, occ in assignment}
        by_name = {name: h for h, name, _, _, _ in assignment}
        by_color = {color: h for h, _, color, _, _ in assignment}
        by_phone = {phone: h for h, _, _, phone, _ in assignment}
        by_occ = {occ: h for h, _, _, _, occ in assignment}
        
        # 1. Engineer is somewhere to the right of lawyer
        if "engineer" in by_occ and "lawyer" in by_occ:
            if by_occ["engineer"] <= by_occ["lawyer"]:
                return False
        
        # 2. Bob is in the second house
        if by_name.get("Bob") != 2:
            return False
        
        # 3. Samsung Galaxy S21 user is doctor
        samsung_house = by_phone.get("samsung galaxy s21")
        doctor_house = by_occ.get("doctor")
        if samsung_house is None or doctor_house is None or samsung_house != doctor_house:
            return False
        
        # 4. Doctor loves blue
        if doctor_house is not None:
            if by_color.get("blue") != doctor_house:
                return False
        
        # 5. Green is not in fifth house
        if by_color.get("green") == 5:
            return False
        
        # 6. Lawyer uses OnePlus 9
        lawyer_house = by_occ.get("lawyer")
        oneplus_house = by_phone.get("oneplus 9")
        if lawyer_house is None or oneplus_house is None or lawyer_house != oneplus_house:
            return False
        
        # 7. Blue is directly left of red
        blue_house = by_color.get("blue")
        red_house = by_color.get("red")
        if blue_house is None or red_house is None or red_house != blue_house + 1:
            return False
        
        # 8. Lawyer is somewhere to the right of Samsung Galaxy S21 user
        if lawyer_house is not None and samsung_house is not None:
            if lawyer_house <= samsung_house:
                return False
        
        # 9. One house between Google Pixel 6 and Huawei P50
        pixel_house = by_phone.get("google pixel 6")
        huawei_house = by_phone.get("huawei p50")
        if pixel_house is not None and huawei_house is not None:
            if abs(pixel_house - huawei_house) != 2:
                return False
        
        # 10. Arnold is engineer
        if by_name.get("Arnold") != by_occ.get("engineer"):
            return False
        
        # 11. Alice loves yellow
        if by_name.get("Alice") != by_color.get("yellow"):
            return False
        
        # 12. Google Pixel 6 is Eric
        if by_phone.get("google pixel 6") != by_name.get("Eric"):
            return False
        
        # 13. Google Pixel 6 user is teacher
        if pixel_house is not None:
            if by_occ.get("teacher") != pixel_house:
                return False
        
        # 14. Red is somewhere to the right of teacher
        teacher_house = by_occ.get("teacher")
        if red_house is not None and teacher_house is not None:
            if red_house <= teacher_house:
                return False
        
        return True
    
    # Backtracking search
    def backtrack(house_idx, used_names, used_colors, used_phones, used_occs, current):
        if house_idx > 5:
            # All houses assigned, check all constraints
            if check_constraints(current):
                return current
            return None
        
        # Try all combinations for this house
        for name in names:
            if name in used_names:
                continue
            for color in colors:
                if color in used_colors:
                    continue
                for phone in phones:
                    if phone in used_phones:
                        continue
                    for occ in occupations:
                        if occ in used_occs:
                            continue
                        
                        # Quick pruning based on some constraints
                        # Constraint 2: Bob must be in house 2
                        if house_idx == 2 and name != "Bob":
                            continue
                        if name == "Bob" and house_idx != 2:
                            continue
                        
                        # Constraint 10: Arnold is engineer
                        if name == "Arnold" and occ != "engineer":
                            continue
                        if occ == "engineer" and name != "Arnold":
                            continue
                        
                        # Constraint 11: Alice loves yellow
                        if name == "Alice" and color != "yellow":
                            continue
                        if color == "yellow" and name != "Alice":
                            continue
                        
                        # Constraint 12: Google Pixel 6 is Eric
                        if phone == "google pixel 6" and name != "Eric":
                            continue
                        if name == "Eric" and phone != "google pixel 6":
                            continue
                        
                        # Constraint 13: Google Pixel 6 user is teacher
                        if phone == "google pixel 6" and occ != "teacher":
                            continue
                        if occ == "teacher" and phone != "google pixel 6":
                            continue
                        
                        # Constraint 3 & 4: Samsung user is doctor who loves blue
                        if phone == "samsung galaxy s21" and (occ != "doctor" or color != "blue"):
                            continue
                        if occ == "doctor" and (phone != "samsung galaxy s21" or color != "blue"):
                            continue
                        if color == "blue" and (phone != "samsung galaxy s21" or occ != "doctor"):
                            continue
                        
                        # Constraint 6: Lawyer uses OnePlus 9
                        if occ == "lawyer" and phone != "oneplus 9":
                            continue
                        if phone == "oneplus 9" and occ != "lawyer":
                            continue
                        
                        new_used_names = used_names | {name}
                        new_used_colors = used_colors | {color}
                        new_used_phones = used_phones | {phone}
                        new_used_occs = used_occs | {occ}
                        new_current = current + [(house_idx, name, color, phone, occ)]
                        
                        result = backtrack(house_idx + 1, new_used_names, new_used_colors, 
                                         new_used_phones, new_used_occs, new_current)
                        if result is not None:
                            return result
        return None
    
    # Start search
    solution = backtrack(1, set(), set(), set(), set(), [])
    
    if solution is None:
        return {"solution": {"header": [], "rows": []}}
    
    # Format solution
    rows = []
    for house, name, color, phone, occ in solution:
        rows.append([str(house), name, color, phone, occ])
    
    # Sort by house number
    rows.sort(key=lambda x: int(x[0]))
    
    result = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))