from z3 import *

# Create an integer variable for each attribute value.
# Each variable represents the house number (1 to 6) where that attribute is placed.

# Names
Arnold   = Int('Arnold')
Carol    = Int('Carol')
Peter    = Int('Peter')
Eric     = Int('Eric')
Bob      = Int('Bob')
Alice    = Int('Alice')

# House Styles
ranch          = Int('ranch')
colonial       = Int('colonial')
modern         = Int('modern')
craftsman      = Int('craftsman')
mediterranean  = Int('mediterranean')
victorian      = Int('victorian')

# Foods
pizza           = Int('pizza')
stew            = Int('stew')
spaghetti       = Int('spaghetti')
grilled_cheese  = Int('grilled_cheese')
stir_fry        = Int('stir_fry')
soup            = Int('soup')

# Vacations
cultural  = Int('cultural')
cruise    = Int('cruise')
mountain  = Int('mountain')
camping   = Int('camping')
city      = Int('city')
beach     = Int('beach')

# Heights
average    = Int('average')
very_tall  = Int('very_tall')
very_short = Int('very_short')
short      = Int('short')
tall       = Int('tall')
super_tall = Int('super_tall')

# Cigars
yellow_monster = Int('yellow_monster')
prince         = Int('prince')
dunhill        = Int('dunhill')
pall_mall      = Int('pall_mall')
blue_master    = Int('blue_master')
blends         = Int('blends')

# List all variables in each category for the distinct constraints and domain restrictions.
names = [Arnold, Carol, Peter, Eric, Bob, Alice]
styles = [ranch, colonial, modern, craftsman, mediterranean, victorian]
foods = [pizza, stew, spaghetti, grilled_cheese, stir_fry, soup]
vacs = [cultural, cruise, mountain, camping, city, beach]
heights = [average, very_tall, very_short, short, tall, super_tall]
cigars = [yellow_monster, prince, dunhill, pall_mall, blue_master, blends]

all_vars = names + styles + foods + vacs + heights + cigars

solver = Solver()

# All variables must be in the domain 1..6.
for var in all_vars:
    solver.add(And(var >= 1, var <= 6))

# All items in each category must be assigned to different houses.
solver.add(Distinct(*names))
solver.add(Distinct(*styles))
solver.add(Distinct(*foods))
solver.add(Distinct(*vacs))
solver.add(Distinct(*heights))
solver.add(Distinct(*cigars))

# Now add the clues as constraints:

# 1. Alice is in the fifth house.
solver.add(Alice == 5)

# 2. The person who loves stir fry is the person living in a colonial-style house.
solver.add(stir_fry == colonial)

# 3. Alice is the person who loves the spaghetti eater.
#    (Interpreted: Alice eats spaghetti.)
solver.add(spaghetti == Alice)

# 4. Arnold is the person who loves the stew.
solver.add(stew == Arnold)

# 5. There is one house between the person who has an average height and Peter.
solver.add(Abs(average - Peter) == 2)

# 6. The person in a Craftsman-style house is not in the third house.
solver.add(craftsman != 3)

# 7. The person who has an average height is the person who loves stir fry.
solver.add(average == stir_fry)

# 8. The person who loves beach vacations is the person in a ranch-style home.
solver.add(beach == ranch)

# 9. Eric is in the fourth house.
solver.add(Eric == 4)

# 10. There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
solver.add(Abs(colonial - camping) == 2)

# 11. The person who enjoys mountain retreats is the person who smokes Yellow Monster.
solver.add(mountain == yellow_monster)

# 12. The person who enjoys mountain retreats is the person who is very tall.
solver.add(mountain == very_tall)

# 13. The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
solver.add(Abs(mountain - dunhill) == 1)

# 14. The person who loves the spaghetti eater is the person residing in a Victorian house.
solver.add(spaghetti == victorian)

# 15. The person who is tall is the person who loves beach vacations.
solver.add(tall == beach)

# 16. The person who is tall is somewhere to the left of the person residing in a Victorian house.
solver.add(tall < victorian)

# 17. The person who loves stir fry is directly left of Bob.
solver.add(Bob == stir_fry + 1)

# 18. The person in a modern-style house is somewhere to the left of Alice.
solver.add(modern < Alice)

# 19. The person in a Craftsman-style house is somewhere to the left of the person who is short.
solver.add(craftsman < short)

# 20. The person who loves stir fry is somewhere to the left of the Prince smoker.
solver.add(stir_fry < prince)

# 21. There are two houses between the person who loves eating grilled cheese and the person who is super tall.
solver.add(Abs(grilled_cheese - super_tall) == 3)

# 22. The person in a ranch-style home is the person who smokes Blue Master.
solver.add(ranch == blue_master)

# 23. The person who smokes many unique blends is directly left of the person who smokes Blue Master.
solver.add(blends == blue_master - 1)

# 24. The person who goes on cultural tours is the person who is a pizza lover.
solver.add(cultural == pizza)

# 25. The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
solver.add(pizza < cruise)

# Check if the solver can find a solution.
if solver.check() == sat:
    model = solver.model()
    # We will create a mapping from house (1 to 6) to each attribute.
    # Each category: (variable, its name as string).
    names_list = [(Arnold, "Arnold"), (Carol, "Carol"), (Peter, "Peter"), (Eric, "Eric"), (Bob, "Bob"), (Alice, "Alice")]
    styles_list = [(ranch, "ranch"), (colonial, "colonial"), (modern, "modern"), (craftsman, "craftsman"), (mediterranean, "mediterranean"), (victorian, "victorian")]
    foods_list = [(pizza, "pizza"), (stew, "stew"), (spaghetti, "spaghetti"), (grilled_cheese, "grilled cheese"), (stir_fry, "stir fry"), (soup, "soup")]
    vacs_list = [(cultural, "cultural"), (cruise, "cruise"), (mountain, "mountain"), (camping, "camping"), (city, "city"), (beach, "beach")]
    heights_list = [(average, "average"), (very_tall, "very tall"), (very_short, "very short"), (short, "short"), (tall, "tall"), (super_tall, "super tall")]
    cigars_list = [(yellow_monster, "yellow monster"), (prince, "prince"), (dunhill, "dunhill"), (pall_mall, "pall mall"), (blue_master, "blue master"), (blends, "blends")]

    # Prepare a dictionary for houses 1..6.
    houses = {i: {} for i in range(1, 7)}

    # For each category, fill in the correct attribute in the corresponding house.
    for var, val in names_list:
        house_num = model[var].as_long()
        houses[house_num]["Name"] = val
    for var, val in styles_list:
        house_num = model[var].as_long()
        houses[house_num]["HouseStyle"] = val
    for var, val in foods_list:
        house_num = model[var].as_long()
        houses[house_num]["Food"] = val
    for var, val in vacs_list:
        house_num = model[var].as_long()
        houses[house_num]["Vacation"] = val
    for var, val in heights_list:
        house_num = model[var].as_long()
        houses[house_num]["Height"] = val
    for var, val in cigars_list:
        house_num = model[var].as_long()
        houses[house_num]["Cigar"] = val

    # Prepare the output in the required JSON structure.
    # The header must be: ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"]
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }

    # Houses are numbered 1 to 6 (from left to right)
    for i in range(1, 7):
        row = [
            str(i),
            houses[i].get("Name", ""),
            houses[i].get("HouseStyle", ""),
            houses[i].get("Food", ""),
            houses[i].get("Vacation", ""),
            houses[i].get("Height", ""),
            houses[i].get("Cigar", "")
        ]
        output["solution"]["rows"].append(row)

    # Print the JSON result.
    import json
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")