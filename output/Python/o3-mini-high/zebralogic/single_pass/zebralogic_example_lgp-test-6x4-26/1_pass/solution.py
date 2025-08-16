#!/usr/bin/env python3
import json
import itertools

def main():
    # There are 6 houses, indexed 0-5 (House number = index+1)
    # Fixed birthdays based on the clues (derived by logical reasoning):
    # House1: feb, House2: may, House3: mar, House4: jan, House5: april, House6: sept
    fixed_birthdays = ["feb", "may", "mar", "jan", "april", "sept"]
    
    # We will build a list "houses" of 6 dictionaries.
    houses = [{} for _ in range(6)]
    for i in range(6):
        houses[i]["House"] = str(i+1)
        houses[i]["Birthday"] = fixed_birthdays[i]
    
    # Fixed Names from clues:
    # Clue5: Carol is in the third house (index 2)
    # Clue14: Peter lives in the colonial house, which we will fix in House2 (index 1)
    # Clue11 & Clue18: The Craftsman house is Arnold in the fourth house (index 3)
    # Clue8: Eric is in the sixth house (index 5)
    houses[1]["Name"] = "Peter"
    houses[2]["Name"] = "Carol"
    houses[3]["Name"] = "Arnold"
    houses[5]["Name"] = "Eric"
    # The remaining two houses (House1 and House5 -> indices 0 and 4) must be assigned to Bob and Alice.
    free_name_indices = [0, 4]
    free_names = ["Bob", "Alice"]
    
    # Fixed HouseStyles:
    # Clue4: The Colonial house is in the second house (index 1)
    # Clue18: The Craftsman house is in the fourth house (index 3)
    houses[1]["HouseStyle"] = "colonial"
    houses[3]["HouseStyle"] = "craftsman"
    # For the remaining houses, the available styles are:
    # {victorian, ranch, modern, mediterranean} (each exactly once).
    free_style_indices = [0, 2, 4, 5]
    style_options = ["victorian", "ranch", "modern", "mediterranean"]
    
    # Fixed Pet:
    # Clue19: The dog is in the fourth house (index 3)
    houses[3]["Pet"] = "dog"
    # The remaining pets to be assigned (once each) are:
    # {bird, cat, rabbit, fish, hamster}
    free_pet_indices = [0, 1, 2, 4, 5]
    pet_options = ["bird", "cat", "rabbit", "fish", "hamster"]
    
    # Now we iterate over the possible assignments for the free categories.
    for names_perm in itertools.permutations(free_names):
        # assign free names to houses at indices 0 and 4
        houses[0]["Name"] = names_perm[0]
        houses[4]["Name"] = names_perm[1]
        # Constraint from Clue7: Fish is somewhere to the right of Bob.
        # This forces Bob to be in an earlier house.
        if houses[0]["Name"] != "Bob":
            # If Bob is not in the first house, then he would be in house5 (index 4),
            # and then any fish would have to be in a house to its right—only possibility would be house6.
            # That possibility will fail later because of other constraints.
            continue
        
        for style_perm in itertools.permutations(style_options):
            # assign free styles in order for indices: 0, 2, 4, 5
            houses[0]["HouseStyle"] = style_perm[0]
            houses[2]["HouseStyle"] = style_perm[1]
            houses[4]["HouseStyle"] = style_perm[2]
            houses[5]["HouseStyle"] = style_perm[3]
            # Constraint: Clue10 forces that there are two houses between the Victorian house and the house with the hamster.
            # Logical analysis forces the Victorian house to be House3 (index 2) and the hamster to be in House6 (index 5).
            if houses[2]["HouseStyle"] != "victorian":
                continue
            # Constraint from Clue12: The Colonial house (House2, index 1) is to the left of the Modern house.
            # Hence, the Modern house must be in a higher numbered house.
            # Since House2 is index 1 and House3 is already victorian, modern must appear in one of houses 5 or 6 (indices 4 or 5).
            if houses[0]["HouseStyle"] == "modern":
                continue
            # Find the index of the Modern house.
            modern_index = None
            for i in range(6):
                if houses[i].get("HouseStyle") == "modern":
                    modern_index = i
                    break
            if modern_index is None or modern_index <= 1:
                continue
            # Clue6: The Mediterranean-style house is NOT in the sixth house.
            if houses[5]["HouseStyle"] == "mediterranean":
                continue
            
            for pet_perm in itertools.permutations(pet_options):
                # assign free pets in order for indices: 0, 1, 2, 4, 5
                houses[0]["Pet"] = pet_perm[0]
                houses[1]["Pet"] = pet_perm[1]
                houses[2]["Pet"] = pet_perm[2]
                houses[4]["Pet"] = pet_perm[3]
                houses[5]["Pet"] = pet_perm[4]
                # Clue1: The pet hamster is somewhere to the right of the person whose birthday is in March.
                # House with birthday "mar" is House3 (index 2); so the hamster must be in an index > 2.
                hamster_index = None
                for i in range(6):
                    if houses[i].get("Pet") == "hamster":
                        hamster_index = i
                        break
                if hamster_index is None or hamster_index <= 2:
                    continue
                # Clue10: There are two houses between the Victorian house and the house with the hamster.
                # We already require Victorian to be in House3, index 2.
                if abs(2 - hamster_index) != 3:
                    continue
                # Clue7: The person with the pet fish is somewhere to the right of Bob.
                fish_index = None
                for i in range(6):
                    if houses[i].get("Pet") == "fish":
                        fish_index = i
                        break
                if fish_index is None or fish_index <= 0:  # Bob is in House1 (index0)
                    continue
                # Clue13: The fish is not in the second house (index 1).
                if houses[1].get("Pet") == "fish":
                    continue
                # Clue9: There is one house between the person who has a cat and the person residing in the Victorian house.
                # Victorian house is in House3 (index 2), so the cat must be in House1 (index 0) or House5 (index 4).
                cat_index = None
                for i in range(6):
                    if houses[i].get("Pet") == "cat":
                        cat_index = i
                        break
                if cat_index is None or abs(cat_index - 2) != 2:
                    continue
                # Clue16: There is one house between the person who keeps a pet bird and the person in the Modern-style house.
                bird_index = None
                for i in range(6):
                    if houses[i].get("Pet") == "bird":
                        bird_index = i
                        break
                if bird_index is None or abs(bird_index - modern_index) != 2:
                    continue
                
                # Clue15: The person whose birthday is in January is directly left of the person whose birthday is in April.
                jan_index = None
                april_index = None
                for i in range(6):
                    if houses[i]["Birthday"] == "jan":
                        jan_index = i
                    if houses[i]["Birthday"] == "april":
                        april_index = i
                if jan_index is None or april_index is None or (april_index - jan_index) != 1:
                    continue
                # Clue2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
                sept_index = None
                for i in range(6):
                    if houses[i]["Birthday"] == "sept":
                        sept_index = i
                        break
                if sept_index is None or jan_index >= sept_index:
                    continue
                
                # Clue12: The Colonial house (House2, index 1) is to the left of the Modern house.
                if modern_index <= 1:
                    continue
                
                # Clue14: Peter is in the Colonial house.
                if houses[1]["Name"] != "Peter" or houses[1]["HouseStyle"] != "colonial":
                    continue
                # Clue5 and Clue17: Carol is in the third house with birthday "mar".
                if houses[2]["Name"] != "Carol" or houses[2]["Birthday"] != "mar":
                    continue
                # Clue8: Eric is in the sixth house.
                if houses[5]["Name"] != "Eric":
                    continue
                # Clue11 & Clue18: The Craftsman-style house (House4, index 3) is Arnold.
                if houses[3]["Name"] != "Arnold":
                    continue
                # Clue19: The fourth house (index 3) has the dog.
                if houses[3]["Pet"] != "dog":
                    continue
                
                # If we reach this point, all constraints are satisfied.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                        "rows": []
                    }
                }
                # Append rows in order from House1 to House6
                for i in range(6):
                    row = [
                        houses[i]["House"],
                        houses[i]["Name"],
                        houses[i]["Pet"],
                        houses[i]["HouseStyle"],
                        houses[i]["Birthday"]
                    ]
                    solution["solution"]["rows"].append(row)
                print(json.dumps(solution))
                return

if __name__ == "__main__":
    main()