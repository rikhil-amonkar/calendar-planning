import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for hobby_perm in permutations(hobbies):
                for education_perm in permutations(educations):
                    for drink_perm in permutations(drinks):
                        # Create assignment for house 1, 2, 3
                        assignment = []
                        for i in range(3):
                            house = {
                                "house": str(i + 1),
                                "name": name_perm[i],
                                "cigar": cigar_perm[i],
                                "hobby": hobby_perm[i],
                                "education": education_perm[i],
                                "drink": drink_perm[i]
                            }
                            assignment.append(house)
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The person partial to Pall Mall is Peter.
                        pall_mall_house = None
                        peter_house = None
                        for house in assignment:
                            if house["cigar"] == "pall mall":
                                pall_mall_house = house
                            if house["name"] == "Peter":
                                peter_house = house
                        if pall_mall_house != peter_house:
                            valid = False
                            continue
                        
                        # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
                        milk_house = None
                        hs_house = None
                        for house in assignment:
                            if house["drink"] == "milk":
                                milk_house = house
                            if house["education"] == "high school":
                                hs_house = house
                        if not milk_house or not hs_house or int(milk_house["house"]) + 1 != int(hs_house["house"]):
                            valid = False
                            continue
                        
                        # Clue 3: Eric is the tea drinker.
                        eric_house = None
                        tea_house = None
                        for house in assignment:
                            if house["name"] == "Eric":
                                eric_house = house
                            if house["drink"] == "tea":
                                tea_house = house
                        if eric_house != tea_house:
                            valid = False
                            continue
                        
                        # Clue 4: Arnold and the Prince smoker are next to each other.
                        arnold_house = None
                        prince_house = None
                        for house in assignment:
                            if house["name"] == "Arnold":
                                arnold_house = house
                            if house["cigar"] == "prince":
                                prince_house = house
                        if not arnold_house or not prince_house or abs(int(arnold_house["house"]) - int(prince_house["house"])) != 1:
                            valid = False
                            continue
                        
                        # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                        gardening_house = None
                        for house in assignment:
                            if house["hobby"] == "gardening":
                                gardening_house = house
                        if not gardening_house or not prince_house or int(gardening_house["house"]) >= int(prince_house["house"]):
                            valid = False
                            continue
                        
                        # Clue 6: The person who likes milk is the person with an associate's degree.
                        associate_house = None
                        for house in assignment:
                            if house["education"] == "associate":
                                associate_house = house
                        if milk_house != associate_house:
                            valid = False
                            continue
                        
                        # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                        bachelor_house = None
                        photography_house = None
                        for house in assignment:
                            if house["education"] == "bachelor":
                                bachelor_house = house
                            if house["hobby"] == "photography":
                                photography_house = house
                        if not bachelor_house or not photography_house or int(bachelor_house["house"]) + 1 != int(photography_house["house"]):
                            valid = False
                            continue
                        
                        if valid:
                            # Format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                                    "rows": []
                                }
                            }
                            
                            for house in sorted(assignment, key=lambda x: int(x["house"])):
                                row = [
                                    house["house"],
                                    house["name"],
                                    house["cigar"],
                                    house["hobby"],
                                    house["education"],
                                    house["drink"]
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print("No solution found")

if __name__ == "__main__":
    main()