import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    book_genres = ["science fiction", "romance", "mystery"]
    phone_models = ["google pixel 6", "iphone 13", "samsung galaxy s21"]
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for animal_perm in permutations(animals):
                for child_perm in permutations(children):
                    for book_perm in permutations(book_genres):
                        for phone_perm in permutations(phone_models):
                            # Create assignment dictionaries
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    "name": name_perm[i],
                                    "cigar": cigar_perm[i],
                                    "animal": animal_perm[i],
                                    "child": child_perm[i],
                                    "book": book_perm[i],
                                    "phone": phone_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person who loves mystery books is the person's child is named Fred.
                            mystery_book_house = None
                            for house, attrs in assignment.items():
                                if attrs["book"] == "mystery":
                                    mystery_book_house = house
                                    break
                            if mystery_book_house is None or assignment[mystery_book_house]["child"] != "Fred":
                                valid = False
                                continue
                            
                            # Clue 2: The cat lover is Eric.
                            cat_house = None
                            for house, attrs in assignment.items():
                                if attrs["animal"] == "cat":
                                    cat_house = house
                                    break
                            if cat_house is None or assignment[cat_house]["name"] != "Eric":
                                valid = False
                                continue
                            
                            # Clue 3: The person partial to Pall Mall is in the second house.
                            if assignment[2]["cigar"] != "pall mall":
                                valid = False
                                continue
                            
                            # Clue 4: The person who keeps horses is the person's child is named Meredith.
                            horse_house = None
                            for house, attrs in assignment.items():
                                if attrs["animal"] == "horse":
                                    horse_house = house
                                    break
                            if horse_house is None or assignment[horse_house]["child"] != "Meredith":
                                valid = False
                                continue
                            
                            # Clue 5: The person's child is named Bella is the Prince smoker.
                            bella_house = None
                            for house, attrs in assignment.items():
                                if attrs["child"] == "Bella":
                                    bella_house = house
                                    break
                            if bella_house is None or assignment[bella_house]["cigar"] != "prince":
                                valid = False
                                continue
                            
                            # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
                            iphone_house = None
                            samsung_house = None
                            for house, attrs in assignment.items():
                                if attrs["phone"] == "iphone 13":
                                    iphone_house = house
                                elif attrs["phone"] == "samsung galaxy s21":
                                    samsung_house = house
                            
                            if iphone_house is None or samsung_house is None or iphone_house + 1 != samsung_house:
                                valid = False
                                continue
                            
                            # Clue 7: The person's child is named Fred is directly left of Arnold.
                            fred_house = None
                            arnold_house = None
                            for house, attrs in assignment.items():
                                if attrs["child"] == "Fred":
                                    fred_house = house
                                elif attrs["name"] == "Arnold":
                                    arnold_house = house
                            
                            if fred_house is None or arnold_house is None or fred_house + 1 != arnold_house:
                                valid = False
                                continue
                            
                            # Clue 8: Peter is somewhere to the left of Eric.
                            peter_house = None
                            eric_house = None
                            for house, attrs in assignment.items():
                                if attrs["name"] == "Peter":
                                    peter_house = house
                                elif attrs["name"] == "Eric":
                                    eric_house = house
                            
                            if peter_house is None or eric_house is None or peter_house >= eric_house:
                                valid = False
                                continue
                            
                            # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
                            scifi_house = None
                            for house, attrs in assignment.items():
                                if attrs["book"] == "science fiction":
                                    scifi_house = house
                                    break
                            if scifi_house is None or assignment[scifi_house]["phone"] != "samsung galaxy s21":
                                valid = False
                                continue
                            
                            # Clue 10: The person who loves science fiction books is in the third house.
                            if scifi_house != 3:
                                valid = False
                                continue
                            
                            # Clue 11: The person who loves mystery books is not in the second house.
                            if mystery_book_house == 2:
                                valid = False
                                continue
                            
                            if valid:
                                # Format the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                        "rows": []
                                    }
                                }
                                
                                for house in sorted(assignment.keys()):
                                    attrs = assignment[house]
                                    row = [
                                        str(house),
                                        attrs["name"],
                                        attrs["cigar"],
                                        attrs["animal"],
                                        attrs["child"],
                                        attrs["book"],
                                        attrs["phone"]
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return
    
    print("No solution found")

if __name__ == "__main__":
    main()