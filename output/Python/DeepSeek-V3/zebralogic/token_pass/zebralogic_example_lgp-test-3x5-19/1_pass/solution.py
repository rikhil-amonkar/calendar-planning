import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]
    
    houses = [1, 2, 3]
    
    # Generate all permutations for each category
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for edu_perm in permutations(educations):
                for sm_perm in permutations(smoothies):
                    for hobby_perm in permutations(hobbies):
                        # Create assignment for each house
                        assignment = []
                        for i in range(3):
                            assignment.append({
                                "house": houses[i],
                                "name": name_perm[i],
                                "occupation": occ_perm[i],
                                "education": edu_perm[i],
                                "smoothie": sm_perm[i],
                                "hobby": hobby_perm[i]
                            })
                        
                        # Check all clues
                        # 1. The Desert smoothie lover is the person who is a doctor.
                        clue1 = True
                        for house in assignment:
                            if house["smoothie"] == "desert" and house["occupation"] != "doctor":
                                clue1 = False
                                break
                            if house["occupation"] == "doctor" and house["smoothie"] != "desert":
                                clue1 = False
                                break
                        if not clue1:
                            continue
                        
                        # 2. Arnold is not in the third house.
                        if assignment[2]["name"] == "Arnold":
                            continue
                        
                        # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
                        peter_house = None
                        cherry_house = None
                        for house in assignment:
                            if house["name"] == "Peter":
                                peter_house = house["house"]
                            if house["smoothie"] == "cherry":
                                cherry_house = house["house"]
                        if peter_house is None or cherry_house is None or cherry_house <= peter_house:
                            continue
                        
                        # 4. The person who loves cooking is in the second house.
                        if assignment[1]["hobby"] != "cooking":
                            continue
                        
                        # 5. The person who loves cooking is Peter.
                        cooking_person = None
                        for house in assignment:
                            if house["hobby"] == "cooking":
                                cooking_person = house["name"]
                        if cooking_person != "Peter":
                            continue
                        
                        # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
                        gardening_house = None
                        associate_house = None
                        for house in assignment:
                            if house["hobby"] == "gardening":
                                gardening_house = house["house"]
                            if house["education"] == "associate":
                                associate_house = house["house"]
                        if gardening_house is None or associate_house is None or associate_house <= gardening_house:
                            continue
                        
                        # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
                        desert_house = None
                        bachelor_house = None
                        for house in assignment:
                            if house["smoothie"] == "desert":
                                desert_house = house["house"]
                            if house["education"] == "bachelor":
                                bachelor_house = house["house"]
                        if desert_house is None or bachelor_house is None or bachelor_house <= desert_house:
                            continue
                        
                        # 8. The person who loves cooking is the person who is a doctor.
                        if assignment[1]["occupation"] != "doctor":
                            continue
                        
                        # 9. The photography enthusiast is the person who is a teacher.
                        for house in assignment:
                            if house["hobby"] == "photography" and house["occupation"] != "teacher":
                                clue9 = False
                                break
                            if house["occupation"] == "teacher" and house["hobby"] != "photography":
                                clue9 = False
                                break
                        else:
                            clue9 = True
                        
                        if not clue9:
                            continue
                        
                        # All clues satisfied - found solution
                        # Sort by house number
                        assignment.sort(key=lambda x: x["house"])
                        
                        # Prepare output
                        rows = []
                        for house in assignment:
                            rows.append([
                                str(house["house"]),
                                house["name"],
                                house["occupation"],
                                house["education"],
                                house["smoothie"],
                                house["hobby"]
                            ])
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                                "rows": rows
                            }
                        }
                        
                        return result
    
    # If no solution found
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))