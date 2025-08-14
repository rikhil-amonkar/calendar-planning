#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes for the houses
    houses = [1, 2]
    names = ['Arnold', 'Eric']
    occupations = ['engineer', 'doctor']
    birthday_months = ['april', 'sept']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    favorite_cigars = ['pall mall', 'prince']

    solutions = []
    
    # Iterate over all possible permutations for each category
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for birthday_perm in itertools.permutations(birthday_months):
                for style_perm in itertools.permutations(house_styles):
                    for height_perm in itertools.permutations(heights):
                        for cigar_perm in itertools.permutations(favorite_cigars):
                            candidate = []
                            for i in range(2):
                                candidate.append({
                                    "House": str(houses[i]),
                                    "Name": name_perm[i],
                                    "Occupation": occ_perm[i],
                                    "Birthday month": birthday_perm[i],
                                    "House style": style_perm[i],
                                    "Height": height_perm[i],
                                    "Favorite cigar": cigar_perm[i]
                                })
                            
                            valid = True
                            
                            # Clue 1: The person who is an engineer is in the first house.
                            if candidate[0]["Occupation"] != "engineer":
                                valid = False
                            
                            # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                            try:
                                april_index = next(i for i, d in enumerate(candidate) if d["Birthday month"] == "april")
                                doctor_index = next(i for i, d in enumerate(candidate) if d["Occupation"] == "doctor")
                            except StopIteration:
                                valid = False
                            else:
                                if abs(april_index - doctor_index) != 1:
                                    valid = False
                            
                            # Clue 3: The person living in a colonial-style house is the person who is an engineer.
                            for d in candidate:
                                if d["House style"] == "colonial" and d["Occupation"] != "engineer":
                                    valid = False
                                    break
                                if d["Occupation"] == "engineer" and d["House style"] != "colonial":
                                    valid = False
                                    break

                            # Clue 4: The person who is very short is the person who is an engineer.
                            for d in candidate:
                                if d["Height"] == "very short" and d["Occupation"] != "engineer":
                                    valid = False
                                    break
                                if d["Occupation"] == "engineer" and d["Height"] != "very short":
                                    valid = False
                                    break
                            
                            # Clue 5: The person who is short is the person partial to Pall Mall.
                            for d in candidate:
                                if d["Height"] == "short" and d["Favorite cigar"] != "pall mall":
                                    valid = False
                                    break
                                if d["Favorite cigar"] == "pall mall" and d["Height"] != "short":
                                    valid = False
                                    break
                            
                            # Clue 6: The person who is an engineer is Eric.
                            for d in candidate:
                                if d["Occupation"] == "engineer" and d["Name"] != "Eric":
                                    valid = False
                                    break
                                if d["Name"] == "Eric" and d["Occupation"] != "engineer":
                                    valid = False
                                    break
                            
                            if valid:
                                solutions.append(candidate)
    
    # Assume a unique solution exists; select the first solution found.
    if solutions:
        solution = solutions[0]
    else:
        solution = []
    
    # Prepare the JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday month", "House style", "Height", "Favorite cigar"],
            "rows": [
                [house["House"], house["Name"], house["Occupation"], house["Birthday month"], house["House style"], house["Height"], house["Favorite cigar"]]
                for house in solution
            ]
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()