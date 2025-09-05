import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for sport_perm in permutations(sports):
                for car_perm in permutations(cars):
                    for flower_perm in permutations(flowers):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                "Name": name_perm[i],
                                "Smoothie": smoothie_perm[i],
                                "FavoriteSport": sport_perm[i],
                                "CarModel": car_perm[i],
                                "Flower": flower_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: Tesla Model 3 owner loves roses
                        tesla_owner = None
                        rose_lover = None
                        for house, attrs in assignment.items():
                            if attrs["CarModel"] == "tesla model 3":
                                tesla_owner = house
                            if attrs["Flower"] == "roses":
                                rose_lover = house
                        if tesla_owner != rose_lover:
                            continue
                        
                        # Clue 2: Peter loves dragonfruit smoothie
                        peter_house = None
                        dragonfruit_lover = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Peter":
                                peter_house = house
                            if attrs["Smoothie"] == "dragonfruit":
                                dragonfruit_lover = house
                        if peter_house != dragonfruit_lover:
                            continue
                        
                        # Clue 3: Desert smoothie lover owns Toyota Camry
                        desert_lover = None
                        toyota_owner = None
                        for house, attrs in assignment.items():
                            if attrs["Smoothie"] == "desert":
                                desert_lover = house
                            if attrs["CarModel"] == "toyota camry":
                                toyota_owner = house
                        if desert_lover != toyota_owner:
                            continue
                        
                        # Clue 4: Tennis lover is in first house
                        if assignment[1]["FavoriteSport"] != "tennis":
                            continue
                        
                        # Clue 5: Toyota Camry owner and basketball lover are adjacent
                        basketball_lover = None
                        for house, attrs in assignment.items():
                            if attrs["FavoriteSport"] == "basketball":
                                basketball_lover = house
                        if abs(toyota_owner - basketball_lover) != 1:
                            continue
                        
                        # Clue 6: Arnold loves basketball
                        arnold_house = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Arnold":
                                arnold_house = house
                        if arnold_house != basketball_lover:
                            continue
                        
                        # Clue 7: Honda Civic owner loves daffodils
                        honda_owner = None
                        daffodil_lover = None
                        for house, attrs in assignment.items():
                            if attrs["CarModel"] == "honda civic":
                                honda_owner = house
                            if attrs["Flower"] == "daffodils":
                                daffodil_lover = house
                        if honda_owner != daffodil_lover:
                            continue
                        
                        # Clue 8: Eric loves roses
                        eric_house = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Eric":
                                eric_house = house
                        if eric_house != rose_lover:
                            continue
                        
                        # Clue 9: Watermelon smoothie lover not in first house
                        watermelon_lover = None
                        for house, attrs in assignment.items():
                            if attrs["Smoothie"] == "watermelon":
                                watermelon_lover = house
                        if watermelon_lover == 1:
                            continue
                        
                        # Clue 10: Honda Civic owner is right of Desert smoothie lover
                        if honda_owner <= desert_lover:
                            continue
                        
                        # Clue 11: Basketball lover loves lilies
                        lily_lover = None
                        for house, attrs in assignment.items():
                            if attrs["Flower"] == "lilies":
                                lily_lover = house
                        if basketball_lover != lily_lover:
                            continue
                        
                        # Clue 12: Tennis and soccer lovers are adjacent
                        soccer_lover = None
                        for house, attrs in assignment.items():
                            if attrs["FavoriteSport"] == "soccer":
                                soccer_lover = house
                        if abs(1 - soccer_lover) != 1:  # tennis is in house 1
                            continue
                        
                        # If we reach here, all constraints are satisfied
                        # Format the solution
                        rows = []
                        for house in sorted(assignment.keys()):
                            attrs = assignment[house]
                            rows.append([
                                str(house),
                                attrs["Name"],
                                attrs["Smoothie"],
                                attrs["FavoriteSport"],
                                attrs["CarModel"],
                                attrs["Flower"]
                            ])
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                                "rows": rows
                            }
                        }
                        
                        print(json.dumps(result, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()