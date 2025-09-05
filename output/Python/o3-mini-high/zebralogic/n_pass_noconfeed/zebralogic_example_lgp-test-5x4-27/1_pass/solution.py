import itertools
import json

# Fixed lists for attributes
names = ["Bob", "Alice", "Eric", "Arnold", "Peter"]
# Birthday months available: "april", "feb", "jan", "mar", "sept"
# Fixed by clues:
# Clue 3: Bob's birthday is april -> House1 must be "april"
# Clue 8: House2 birthday is feb -> House2 = "feb"
# Clue 6: With Peter in House5, and one house between january and Peter, House3 must be "jan"
fixed_birthdays = [None] * 5
fixed_birthdays[0] = "april"  # House1: Bob
fixed_birthdays[1] = "feb"    # House2: Alice
fixed_birthdays[2] = "jan"    # House3: Eric

# For Houses 4 and 5, the remaining birthdays { "mar", "sept" } will be assigned.
birthday_options = list(itertools.permutations(["mar", "sept"], 2))

# Cigars available: "pall mall", "prince", "dunhill", "blends", "blue master"
# Fixed:
# Clue 2: House3 smokes pall mall -> House3: "pall mall"
# Clue 7: The blends smoker has birthday feb -> House2: "blends"
# For Houses 1,4,5 (indexes 0,3,4) we assign from the remaining {"prince", "blue master", "dunhill"}
# Also, by Clue 4: The Dunhill smoker has birthday mar.
cigar_candidates = ["prince", "blue master", "dunhill"]

# Drinks available: "water", "coffee", "tea", "milk", "root beer"
# Fixed:
# Clue 1: Eric (House3) drinks root beer -> House3: "root beer"
drink_candidates = ["water", "coffee", "tea", "milk"]

solution_found = None

# Loop over possible assignments for birthdays for House4 and House5
for bd_option in birthday_options:
    # Construct full birthday list for houses 1..5:
    birthdays = fixed_birthdays.copy()
    birthdays[3] = bd_option[0]
    birthdays[4] = bd_option[1]
    
    # Loop over permutations of cigars for Houses 1,4,5 (indexes 0,3,4) from the 3 candidate cigars.
    # Constraint: House1 (index 0) cannot be "dunhill" because its birthday is "april" (and dunhill must go with "mar").
    for cig_perm in itertools.permutations(cigar_candidates, 3):
        if cig_perm[0] == "dunhill":
            continue
        cigars = [None] * 5
        cigars[0] = cig_perm[0]         # House1
        cigars[1] = "blends"            # House2 (fixed)
        cigars[2] = "pall mall"         # House3 (fixed)
        cigars[3] = cig_perm[1]         # House4
        cigars[4] = cig_perm[2]         # House5
        
        # Clue 4: The Dunhill smoker must have birthday mar.
        if cigars[3] == "dunhill" and birthdays[3] != "mar":
            continue
        if cigars[4] == "dunhill" and birthdays[4] != "mar":
            continue
        
        # Loop over drink assignments for Houses 1,2,4,5 (indexes 0,1,3,4) from drink_candidates.
        # House3 (index 2) is fixed as "root beer".
        for drink_perm in itertools.permutations(drink_candidates, 4):
            drinks = [None] * 5
            drinks[0] = drink_perm[0]    # House1
            drinks[1] = drink_perm[1]    # House2
            drinks[2] = "root beer"      # House3 (fixed)
            drinks[3] = drink_perm[2]    # House4
            drinks[4] = drink_perm[3]    # House5
            
            # Clue 10: The milk drinker is not in the fifth house.
            if drinks[4] == "milk":
                continue
            
            # Clue 11: The Blue Master smoker is the coffee drinker.
            # Check Houses 1,4,5 because these are the ones that can get Blue Master.
            if cigars[0] == "blue master" and drinks[0] != "coffee":
                continue
            if cigars[3] == "blue master" and drinks[3] != "coffee":
                continue
            if cigars[4] == "blue master" and drinks[4] != "coffee":
                continue
            
            # Clue 12: There is one house between the tea drinker and the coffee drinker.
            # Build full drinks list (already in order of houses 1 to 5):
            # Find the indices for "coffee" and "tea"
            if "coffee" not in drinks or "tea" not in drinks:
                continue
            coffee_index = drinks.index("coffee")
            tea_index = drinks.index("tea")
            if abs(coffee_index - tea_index) != 2:
                continue
            
            # All constraints satisfied. Additional clues are already enforced by fixed assignments.
            # (Clue 1: Eric in House3 drinks root beer, Clue 2: House3 smokes pall mall, Clue 3: Bob in House1 has birthday april,
            #  Clue 5: Peter is to the right of the root beer lover, Clue 6: House3 (jan) is one house away from Peter in House5,
            #  Clue 7 & 8: House2 (feb) with blends, Clue 9: Arnold is directly left of Peter, Clue 13: Eric in House3.)
            
            solution_found = {
                "houses": [
                    {"House": "1", "Name": names[0], "Birthday": birthdays[0], "Cigar": cigars[0], "Drink": drinks[0]},
                    {"House": "2", "Name": names[1], "Birthday": birthdays[1], "Cigar": cigars[1], "Drink": drinks[1]},
                    {"House": "3", "Name": names[2], "Birthday": birthdays[2], "Cigar": cigars[2], "Drink": drinks[2]},
                    {"House": "4", "Name": names[3], "Birthday": birthdays[3], "Cigar": cigars[3], "Drink": drinks[3]},
                    {"House": "5", "Name": names[4], "Birthday": birthdays[4], "Cigar": cigars[4], "Drink": drinks[4]},
                ]
            }
            break
        if solution_found:
            break
    if solution_found:
        break

# Prepare output in the required JSON structure.
if solution_found is not None:
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": [
                [house["House"], house["Name"], house["Birthday"], house["Cigar"], house["Drink"]]
                for house in solution_found["houses"]
            ]
        }
    }
    print(json.dumps(output))