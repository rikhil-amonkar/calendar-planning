import itertools
import json

def solve():
    # Define the attributes
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]
    
    # There are 3 houses, positions 0, 1, 2 corresponding to houses "1", "2", "3"
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for hobby_perm in itertools.permutations(hobbies):
                for edu_perm in itertools.permutations(educations):
                    for drink_perm in itertools.permutations(drinks):
                        # Build the list of houses with their attributes
                        houses = []
                        for i in range(3):
                            houses.append({
                                "House": str(i+1),
                                "Name": name_perm[i],
                                "Cigar": cigar_perm[i],
                                "Hobby": hobby_perm[i],
                                "Education": edu_perm[i],
                                "Drink": drink_perm[i]
                            })
                        
                        valid = True
                        
                        # Constraint 1: The person partial to Pall Mall is Peter.
                        # This means that the house with cigar "pall mall" must have Name "Peter"
                        for h in houses:
                            if h["Cigar"] == "pall mall" and h["Name"] != "Peter":
                                valid = False
                                break
                            if h["Name"] == "Peter" and h["Cigar"] != "pall mall":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Constraint 3: Eric is the tea drinker.
                        for h in houses:
                            if h["Name"] == "Eric" and h["Drink"] != "tea":
                                valid = False
                                break
                            if h["Drink"] == "tea" and h["Name"] != "Eric":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Constraint 6: The person who likes milk is the person with an associate's degree.
                        for h in houses:
                            if h["Drink"] == "milk" and h["Education"] != "associate":
                                valid = False
                                break
                            if h["Education"] == "associate" and h["Drink"] != "milk":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Constraint 2: The person who likes milk is directly left of the person with a high school diploma.
                        # i.e., for some house i (0 or 1), house[i] has Drink milk and house[i+1] has Education high school.
                        milk_high_adjacent = False
                        for i in range(2):
                            if houses[i]["Drink"] == "milk" and houses[i+1]["Education"] == "high school":
                                milk_high_adjacent = True
                        if not milk_high_adjacent:
                            continue
                        
                        # Constraint 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                        bachelor_photo_adjacent = False
                        for i in range(2):
                            if houses[i]["Education"] == "bachelor" and houses[i+1]["Hobby"] == "photography":
                                bachelor_photo_adjacent = True
                        if not bachelor_photo_adjacent:
                            continue
                        
                        # Constraint 4: Arnold and the Prince smoker are next to each other.
                        adjacent_pair = False
                        for i in range(3):
                            for j in [i-1, i+1]:
                                if 0 <= j < 3:
                                    if (houses[i]["Name"] == "Arnold" and houses[j]["Cigar"] == "prince") or \
                                       (houses[i]["Cigar"] == "prince" and houses[j]["Name"] == "Arnold"):
                                        adjacent_pair = True
                        if not adjacent_pair:
                            continue
                        
                        # Constraint 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                        index_gardening = None
                        index_prince = None
                        for i, h in enumerate(houses):
                            if h["Hobby"] == "gardening":
                                index_gardening = i
                            if h["Cigar"] == "prince":
                                index_prince = i
                        if index_gardening is None or index_prince is None or index_gardening >= index_prince:
                            continue
                        
                        # If we reach here, all constraints are satisfied.
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                                "rows": [
                                    [houses[0]["House"], houses[0]["Name"], houses[0]["Cigar"], houses[0]["Hobby"], houses[0]["Education"], houses[0]["Drink"]],
                                    [houses[1]["House"], houses[1]["Name"], houses[1]["Cigar"], houses[1]["Hobby"], houses[1]["Education"], houses[1]["Drink"]],
                                    [houses[2]["House"], houses[2]["Name"], houses[2]["Cigar"], houses[2]["Hobby"], houses[2]["Education"], houses[2]["Drink"]]
                                ]
                            }
                        }
                        print(json.dumps(result))
                        return

if __name__ == "__main__":
    solve()