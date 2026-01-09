import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    heights = ["average", "very tall", "very short", "short", "tall"]
    cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]
    
    houses = [1, 2, 3, 4, 5]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"cigar_{house}", cigars)
        problem.addVariable(f"smoothie_{house}", smoothies)
        problem.addVariable(f"phone_{house}", phones)
    
    # All attributes must be different
    for attr in ["name", "height", "cigar", "smoothie", "phone"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The Prince smoker is the Desert smoothie lover.
    for house in houses:
        problem.addConstraint(
            lambda cigar, smoothie: not (cigar == "prince") or (smoothie == "desert"),
            [f"cigar_{house}", f"smoothie_{house}"]
        )
        problem.addConstraint(
            lambda cigar, smoothie: not (smoothie == "desert") or (cigar == "prince"),
            [f"cigar_{house}", f"smoothie_{house}"]
        )
    
    # Clue 2: There is one house between Eric and Alice.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 2:
                problem.addConstraint(
                    lambda name1, name2: (name1 == "Eric" and name2 == "Alice") or (name1 == "Alice" and name2 == "Eric"),
                    [f"name_{house1}", f"name_{house2}"]
                )
    
    # Clue 3: The person who is short is the person who smokes many unique blends.
    for house in houses:
        problem.addConstraint(
            lambda height, cigar: not (height == "short") or (cigar == "blends"),
            [f"height_{house}", f"cigar_{house}"]
        )
        problem.addConstraint(
            lambda height, cigar: not (cigar == "blends") or (height == "short"),
            [f"height_{house}", f"cigar_{house}"]
        )
    
    # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    for house in range(1, 5):
        problem.addConstraint(
            lambda phone, cigar_next: not (phone == "iphone 13") or (cigar_next == "blue master"),
            [f"phone_{house}", f"cigar_{house+1}"]
        )
    
    # Clue 5: The person who has an average height is the Dunhill smoker.
    for house in houses:
        problem.addConstraint(
            lambda height, cigar: not (height == "average") or (cigar == "dunhill"),
            [f"height_{house}", f"cigar_{house}"]
        )
        problem.addConstraint(
            lambda height, cigar: not (cigar == "dunhill") or (height == "average"),
            [f"height_{house}", f"cigar_{house}"]
        )
    
    # Clue 6: Eric is the person who is very tall.
    for house in houses:
        problem.addConstraint(
            lambda name, height: not (name == "Eric") or (height == "very tall"),
            [f"name_{house}", f"height_{house}"]
        )
    
    # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
    for house in range(1, 5):
        problem.addConstraint(
            lambda name, phone_next: not (name == "Arnold") or (phone_next == "huawei p50"),
            [f"name_{house}", f"phone_{house+1}"]
        )
    
    # Clue 8: Bob is not in the fourth house.
    problem.addConstraint(lambda name: name != "Bob", ["name_4"])
    
    # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
    for house in range(1, 5):
        problem.addConstraint(
            lambda name, smoothie_next: not (name == "Eric") or (smoothie_next == "cherry"),
            [f"name_{house}", f"smoothie_{house+1}"]
        )
    
    # Clue 10: Bob is the Dunhill smoker.
    for house in houses:
        problem.addConstraint(
            lambda name, cigar: not (name == "Bob") or (cigar == "dunhill"),
            [f"name_{house}", f"cigar_{house}"]
        )
    
    # Clue 11: The Dragonfruit smoothie lover is Bob.
    for house in houses:
        problem.addConstraint(
            lambda name, smoothie: not (smoothie == "dragonfruit") or (name == "Bob"),
            [f"name_{house}", f"smoothie_{house}"]
        )
    
    # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 1:
                problem.addConstraint(
                    lambda phone1, phone2: not (phone1 == "iphone 13" and phone2 == "oneplus 9") and 
                                          not (phone1 == "oneplus 9" and phone2 == "iphone 13") or 
                                          (abs(house1 - house2) == 1),
                    [f"phone_{house1}", f"phone_{house2}"]
                )
    
    # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
    for house in houses:
        problem.addConstraint(
            lambda phone, height: not (phone == "samsung galaxy s21") or (height == "short"),
            [f"phone_{house}", f"height_{house}"]
        )
        problem.addConstraint(
            lambda phone, height: not (height == "short") or (phone == "samsung galaxy s21"),
            [f"phone_{house}", f"height_{house}"]
        )
    
    # Clue 14: There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 3:
                problem.addConstraint(
                    lambda height1, smoothie2: not (height1 == "very tall") or (smoothie2 == "dragonfruit"),
                    [f"height_{house1}", f"smoothie_{house2}"]
                )
                problem.addConstraint(
                    lambda smoothie1, height2: not (smoothie1 == "dragonfruit") or (height2 == "very tall"),
                    [f"smoothie_{house1}", f"height_{house2}"]
                )
    
    # Clue 15: The person who uses an iPhone 13 is Eric.
    for house in houses:
        problem.addConstraint(
            lambda name, phone: not (phone == "iphone 13") or (name == "Eric"),
            [f"name_{house}", f"phone_{house}"]
        )
    
    # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    for house1 in houses:
        for house2 in houses:
            if house1 < house2:
                problem.addConstraint(
                    lambda smoothie1, smoothie2: not (smoothie1 == "desert" and smoothie2 == "lime") or (house1 < house2),
                    [f"smoothie_{house1}", f"smoothie_{house2}"]
                )
    
    # Clue 17: Arnold and the person who is very short are next to each other.
    for house1 in houses:
        for house2 in houses:
            if abs(house1 - house2) == 1:
                problem.addConstraint(
                    lambda name1, height2: not (name1 == "Arnold") or (height2 == "very short"),
                    [f"name_{house1}", f"height_{house2}"]
                )
                problem.addConstraint(
                    lambda height1, name2: not (height1 == "very short") or (name2 == "Arnold"),
                    [f"height_{house1}", f"name_{house2}"]
                )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"]
    rows = []
    
    for house in range(1, 6):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"height_{house}"],
            solution[f"cigar_{house}"],
            solution[f"smoothie_{house}"],
            solution[f"phone_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))