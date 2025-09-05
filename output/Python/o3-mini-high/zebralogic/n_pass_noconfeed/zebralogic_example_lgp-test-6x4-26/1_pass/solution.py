import itertools
import json

def valid(houses):
    # Constraint 1: Hamster is somewhere to the right of the person whose birthday is in March.
    pos_mar = None
    pos_hamster = None
    for i, h in enumerate(houses):
        if h["Birthday"] == "mar":
            pos_mar = i
        if h["Pet"] == "hamster":
            pos_hamster = i
    if pos_mar is None or pos_hamster is None or not (pos_hamster > pos_mar):
        return False

    # Constraint 2: The person whose birthday is in January is somewhere to the left of the person whose birthday is in September.
    pos_jan = None
    pos_sept = None
    for i, h in enumerate(houses):
        if h["Birthday"] == "jan":
            pos_jan = i
        if h["Birthday"] == "sept":
            pos_sept = i
    if pos_jan is None or pos_sept is None or not (pos_jan < pos_sept):
        return False

    # Constraint 3: The person whose birthday is in May is in the second house.
    if houses[1]["Birthday"] != "may":
        return False

    # Constraint 4: The person living in a colonial-style house is in the second house.
    if houses[1]["HouseStyle"] != "colonial":
        return False

    # Constraint 5: Carol is in the third house.
    if houses[2]["Name"] != "Carol":
        return False

    # Constraint 6: The person in a Mediterranean-style villa is not in the sixth house.
    if houses[5]["HouseStyle"] == "mediterranean":
        return False

    # Constraint 7: The person with an aquarium of fish is somewhere to the right of Bob.
    pos_Bob = None
    pos_fish = None
    for i, h in enumerate(houses):
        if h["Name"] == "Bob":
            pos_Bob = i
        if h["Pet"] == "fish":
            pos_fish = i
    if pos_Bob is None or pos_fish is None or not (pos_fish > pos_Bob):
        return False

    # Constraint 8: Eric is in the sixth house.
    if houses[5]["Name"] != "Eric":
        return False

    # Constraint 9: There is one house between the person who has a cat and the person residing in a Victorian house.
    pos_cat = None
    pos_victorian = None
    for i, h in enumerate(houses):
        if h["Pet"] == "cat":
            pos_cat = i
        if h["HouseStyle"] == "victorian":
            pos_victorian = i
    if pos_cat is None or pos_victorian is None or abs(pos_cat - pos_victorian) != 2:
        return False

    # Constraint 10: There are two houses between the person residing in a Victorian house and the person with a pet hamster.
    if pos_victorian is None or pos_hamster is None or abs(pos_victorian - pos_hamster) != 3:
        return False

    # Constraint 11: The person in a Craftsman-style house is Arnold.
    for h in houses:
        if h["HouseStyle"] == "craftsman" and h["Name"] != "Arnold":
            return False

    # Constraint 12: The person living in a colonial-style house is somewhere to the left of the person in a modern-style house.
    pos_colonial = None
    pos_modern = None
    for i, h in enumerate(houses):
        if h["HouseStyle"] == "colonial":
            pos_colonial = i
        if h["HouseStyle"] == "modern":
            pos_modern = i
    if pos_colonial is None or pos_modern is None or not (pos_colonial < pos_modern):
        return False

    # Constraint 13: The person with an aquarium of fish is not in the second house.
    if houses[1]["Pet"] == "fish":
        return False

    # Constraint 14: Peter is the person living in a colonial-style house.
    for h in houses:
        if h["HouseStyle"] == "colonial" and h["Name"] != "Peter":
            return False

    # Constraint 15: The person whose birthday is in January is directly left of the person whose birthday is in April.
    found_pair = False
    for i in range(len(houses) - 1):
        if houses[i]["Birthday"] == "jan" and houses[i+1]["Birthday"] == "april":
            found_pair = True
    if not found_pair:
        return False

    # Constraint 16: There is one house between the person who keeps a pet bird and the person in a modern-style house.
    pos_bird = None
    pos_modern = None
    for i, h in enumerate(houses):
        if h["Pet"] == "bird":
            pos_bird = i
        if h["HouseStyle"] == "modern":
            pos_modern = i
    if pos_bird is None or pos_modern is None or abs(pos_bird - pos_modern) != 2:
        return False

    # Constraint 17: Carol is the person whose birthday is in March.
    for h in houses:
        if h["Name"] == "Carol" and h["Birthday"] != "mar":
            return False

    # Constraint 18: The person in a Craftsman-style house is in the fourth house.
    if houses[3]["HouseStyle"] != "craftsman":
        return False

    # Constraint 19: The person who owns a dog is in the fourth house.
    if houses[3]["Pet"] != "dog":
        return False

    return True

def main():
    # There are 6 houses, indices 0 to 5 (House 1 to House 6)
    # Fixed attribute values based on direct clues:
    # Names: House2(index1)="Peter", House3(index2)="Carol", House4(index3)="Arnold", House6(index5)="Eric"
    # Remaining names for House1(index0) and House5(index4): "Bob" and "Alice"
    fixed_names = [None] * 6
    fixed_names[1] = "Peter"
    fixed_names[2] = "Carol"
    fixed_names[3] = "Arnold"
    fixed_names[5] = "Eric"
    remaining_names = ["Bob", "Alice"]
    
    # Birthdays: Fixed: House2(index1)="may", House3(index2)="mar"
    # Remaining birthdays for indices [0, 3, 4, 5]: {"sept", "feb", "jan", "april"}
    fixed_birthdays = [None] * 6
    fixed_birthdays[1] = "may"
    fixed_birthdays[2] = "mar"
    remaining_birthdays = ["sept", "feb", "jan", "april"]
    
    # House styles: Fixed: House2(index1)="colonial", House4(index3)="craftsman"
    # Remaining indices [0, 2, 4, 5] get: {"victorian", "ranch", "modern", "mediterranean"}
    fixed_styles = [None] * 6
    fixed_styles[1] = "colonial"
    fixed_styles[3] = "craftsman"
    remaining_styles = ["victorian", "ranch", "modern", "mediterranean"]
    
    # Pets: Fixed: House4(index3)="dog"
    # Remaining indices [0, 1, 2, 4, 5] get: {"bird", "cat", "rabbit", "fish", "hamster"}
    fixed_pets = [None] * 6
    fixed_pets[3] = "dog"
    remaining_pets = ["bird", "cat", "rabbit", "fish", "hamster"]
    
    solution = None

    for names_perm in itertools.permutations(remaining_names, len(remaining_names)):
        names = fixed_names.copy()
        # Indices 0 and 4 are not fixed.
        names[0] = names_perm[0]
        names[4] = names_perm[1]
        
        for bd_perm in itertools.permutations(remaining_birthdays, 4):
            birthdays = fixed_birthdays.copy()
            # The indices to fill: 0, 3, 4, 5 in that order.
            birthdays[0] = bd_perm[0]
            birthdays[3] = bd_perm[1]
            birthdays[4] = bd_perm[2]
            birthdays[5] = bd_perm[3]
            
            for style_perm in itertools.permutations(remaining_styles, 4):
                styles = fixed_styles.copy()
                # Fill indices: 0, 2, 4, 5 (House3's style is not fixed yet)
                styles[0] = style_perm[0]
                styles[2] = style_perm[1]
                styles[4] = style_perm[2]
                styles[5] = style_perm[3]
                
                # Constraint 6 check (Mediterranean not in house6 i.e., index5) can be applied here early.
                if styles[5] == "mediterranean":
                    continue

                for pet_perm in itertools.permutations(remaining_pets, 5):
                    pets = fixed_pets.copy()
                    # Fill indices: 0, 1, 2, 4, 5
                    pets[0] = pet_perm[0]
                    pets[1] = pet_perm[1]
                    pets[2] = pet_perm[2]
                    pets[4] = pet_perm[3]
                    pets[5] = pet_perm[4]
                    
                    # Constraint 13: Fish is not in the second house (index1)
                    if pets[1] == "fish":
                        continue

                    # Build the houses list as a list of dictionaries
                    houses = []
                    for i in range(6):
                        house = {
                            "Name": names[i],
                            "Pet": pets[i],
                            "HouseStyle": styles[i],
                            "Birthday": birthdays[i]
                        }
                        houses.append(house)
                    
                    if valid(houses):
                        # Found the solution; format it in the required JSON structure
                        rows = []
                        for i, h in enumerate(houses):
                            # House numbers are 1-indexed as strings
                            row = [str(i+1), h["Name"], h["Pet"], h["HouseStyle"], h["Birthday"]]
                            rows.append(row)
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()