from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

# Create dictionaries for each attribute
name_vars = {name: Int(f"name_{name}") for name in names}
house_style_vars = {style: Int(f"house_style_{style}") for style in house_styles}
food_vars = {food: Int(f"food_{food}") for food in foods}
vacation_vars = {vacation: Int(f"vacation_{vacation}") for vacation in vacations}
height_vars = {height: Int(f"height_{height}") for height in heights}
cigar_vars = {cigar: Int(f"cigar_{cigar}") for cigar in cigars}

# Add constraints for each attribute to be in a unique house
for var_dict in [name_vars, house_style_vars, food_vars, vacation_vars, height_vars, cigar_vars]:
    solver.add(Distinct([var_dict[attr] for attr in var_dict]))

# Add constraints based on clues
# 1. Alice is in the fifth house.
solver.add(name_vars["Alice"] == 5)

# 2. The person who loves stir fry is the person living in a colonial-style house.
solver.add(food_vars["stir fry"] == house_style_vars["colonial"])

# 3. Alice is the person who loves the spaghetti eater.
solver.add(name_vars["Alice"] == food_vars["spaghetti"])

# 4. Arnold is the person who loves the stew.
solver.add(name_vars["Arnold"] == food_vars["stew"])

# 5. There is one house between the person who has an average height and Peter.
solver.add(Abs(height_vars["average"] - name_vars["Peter"]) == 2)

# 6. The person in a Craftsman-style house is not in the third house.
solver.add(house_style_vars["craftsman"] != 3)

# 7. The person who has an average height is the person who loves stir fry.
solver.add(height_vars["average"] == food_vars["stir fry"])

# 8. The person who loves beach vacations is the person in a ranch-style home.
solver.add(vacation_vars["beach"] == house_style_vars["ranch"])

# 9. Eric is in the fourth house.
solver.add(name_vars["Eric"] == 4)

# 10. There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
solver.add(Abs(house_style_vars["colonial"] - vacation_vars["camping"]) == 2)

# 11. The person who enjoys mountain retreats is the person who smokes Yellow Monster.
solver.add(vacation_vars["mountain"] == cigar_vars["yellow monster"])

# 12. The person who enjoys mountain retreats is the person who is very tall.
solver.add(vacation_vars["mountain"] == height_vars["very tall"])

# 13. The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
solver.add(Abs(vacation_vars["mountain"] - cigar_vars["dunhill"]) == 1)

# 14. The person who loves the spaghetti eater is the person residing in a Victorian house.
solver.add(food_vars["spaghetti"] == house_style_vars["victorian"])

# 15. The person who is tall is the person who loves beach vacations.
solver.add(height_vars["tall"] == vacation_vars["beach"])

# 16. The person who is tall is somewhere to the left of the person residing in a Victorian house.
solver.add(height_vars["tall"] < house_style_vars["victorian"])

# 17. The person who loves stir fry is directly left of Bob.
solver.add(food_vars["stir fry"] + 1 == name_vars["Bob"])

# 18. The person in a modern-style house is somewhere to the left of Alice.
solver.add(house_style_vars["modern"] < name_vars["Alice"])

# 19. The person in a Craftsman-style house is somewhere to the left of the person who is short.
solver.add(house_style_vars["craftsman"] < height_vars["short"])

# 20. The person who loves stir fry is somewhere to the left of the Prince smoker.
solver.add(food_vars["stir fry"] < cigar_vars["prince"])

# 21. There are two houses between the person who loves eating grilled cheese and the person who is super tall.
solver.add(Abs(food_vars["grilled cheese"] - height_vars["super tall"]) == 3)

# 22. The person in a ranch-style home is the person who smokes Blue Master.
solver.add(house_style_vars["ranch"] == cigar_vars["blue master"])

# 23. The person who smokes many unique blends is directly left of the person who smokes Blue Master.
solver.add(cigar_vars["blends"] + 1 == cigar_vars["blue master"])

# 24. The person who goes on cultural tours is the person who is a pizza lover.
solver.add(vacation_vars["cultural"] == food_vars["pizza"])

# 25. The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
solver.add(food_vars["pizza"] < vacation_vars["cruise"])

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        house_info = [str(house)]
        for var_dict in [name_vars, house_style_vars, food_vars, vacation_vars, height_vars, cigar_vars]:
            for attr, var in var_dict.items():
                if model.evaluate(var) == house:
                    house_info.append(attr)
                    break
        solution.append(house_info)
    
    # Print the solution in JSON format
    print('{"solution": {"header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"], "rows": ' + str(solution).replace("'", '"') + '}}')
else:
    print("No solution found")