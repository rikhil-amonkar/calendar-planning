import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]
    houses = [1, 2, 3, 4, 5, 6]
    
    # Generate all permutations for names, heights, phones across 6 houses
    # We'll brute force but with constraint pruning
    solutions = []
    
    # We'll iterate through all possible assignments
    for name_perm in permutations(names, 6):
        # Check clue 9: super tall is in house 1
        # We don't know which name is super tall yet, but we'll check later
        
        for height_perm in permutations(heights, 6):
            # Check clue 9: super tall is in house 1
            if height_perm[0] != "super tall":
                continue
                
            # Check clue 4: Carol is very tall
            carol_index = name_perm.index("Carol")
            if height_perm[carol_index] != "very tall":
                continue
                
            # Check clue 8: tall is Arnold
            arnold_index = name_perm.index("Arnold")
            if height_perm[arnold_index] != "tall":
                continue
                
            # Check clue 12: short is in house 6
            if height_perm[5] != "short":
                continue
                
            for phone_perm in permutations(phones, 6):
                # Check clue 6: Samsung Galaxy S21 is not in first house
                if phone_perm[0] == "samsung galaxy s21":
                    continue
                    
                # Check clue 10: Xiaomi Mi 11 is Carol
                if phone_perm[carol_index] != "xiaomi mi 11":
                    continue
                
                # Create assignment dictionary
                assignment = {}
                for i in range(6):
                    assignment[i] = {
                        'house': i+1,
                        'name': name_perm[i],
                        'height': height_perm[i],
                        'phone': phone_perm[i]
                    }
                
                # Check clue 1: Bob is directly left of the person who is tall
                bob_index = name_perm.index("Bob")
                tall_index = height_perm.index("tall")
                if bob_index + 1 != tall_index:
                    continue
                
                # Check clue 2: Peter is somewhere to the left of iPhone 13 user
                peter_index = name_perm.index("Peter")
                iphone_index = phone_perm.index("iphone 13")
                if not (peter_index < iphone_index):
                    continue
                
                # Check clue 3: very short is somewhere to the right of Google Pixel 6 user
                very_short_index = height_perm.index("very short")
                pixel_index = phone_perm.index("google pixel 6")
                if not (very_short_index > pixel_index):
                    continue
                
                # Check clue 5: one house between Google Pixel 6 and short
                short_index = height_perm.index("short")
                if abs(pixel_index - short_index) != 2:
                    continue
                
                # Check clue 7: OnePlus 9 is directly left of short
                oneplus_index = phone_perm.index("oneplus 9")
                if oneplus_index + 1 != short_index:
                    continue
                
                # Check clue 11: Google Pixel 6 is somewhere to the right of Eric
                eric_index = name_perm.index("Eric")
                if not (pixel_index > eric_index):
                    continue
                
                # All clues satisfied
                solutions.append(assignment)
    
    if not solutions:
        return None
    
    # Convert solution to required format
    solution = solutions[0]  # Should be unique
    
    # Create rows in house order
    rows = []
    for i in range(6):
        rows.append([
            str(i+1),
            solution[i]['name'],
            solution[i]['height'],
            solution[i]['phone']
        ])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    
    return result

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()