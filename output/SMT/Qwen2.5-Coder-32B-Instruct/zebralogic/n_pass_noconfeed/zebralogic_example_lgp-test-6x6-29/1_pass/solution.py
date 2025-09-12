from z3 import *

# Define the domain
houses = range(1, 7)
names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

# Create a solver instance
solver = Solver()

# Declare variables
name_vars = {name: Int(name) for name in names}
style_vars = {style: Int(style) for style in house_styles}
food_vars = {food: Int(food) for food in foods}
vacation_vars = {vacation: Int(vacation) for vacation in vacations}
height_vars = {height: Int(height) for height in heights}
cigar_vars = {cigar: Int(cigar) for cigar in cigars}

# Add constraints for each variable to be in the range [1, 6]
for var in list(name_vars.values()) + list(style_vars.values()) + list(food_vars.values()) + \
           list(vacation_vars.values()) + list(height_vars.values()) + list(cigar_vars.values()):
    solver.add(var >= 1, var <= 6)

# All variables must be distinct
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(style_vars.values())))
solver.add(Distinct(list(food_vars.values())))
solver.add(Distinct(list(vacation_vars.values())))
solver.add(Distinct(list(height_vars.values())))
solver.add(Distinct(list(cigar_vars.values())))

# Clues
solver.add(name_vars["Alice"] == 5)
solver.add(food_vars["stir fry"] == style_vars["colonial"])
solver.add(food_vars["spaghetti"] == name_vars["Alice"])
solver.add(food_vars["stew"] == name_vars["Arnold"])
solver.add(Abs(height_vars["average"] - name_vars["Peter"]) == 1)
solver.add(style_vars["craftsman"] != 3)
solver.add(food_vars["stir fry"] == height_vars["average"])
solver.add(vacation_vars["beach"] == style_vars["ranch"])
solver.add(name_vars["Eric"] == 4)
solver.add(Abs(style_vars["colonial"] - vacation_vars["camping"]) == 1)
solver.add(vacation_vars["mountain"] == cigar_vars["yellow monster"])
solver.add(vacation_vars["mountain"] == height_vars["very tall"])
solver.add(Or(Abs(cigar_vars["dunhill"] - vacation_vars["mountain"]) == 1,
             Abs(vacation_vars["mountain"] - cigar_vars["dunhill"]) == 1))
solver.add(food_vars["spaghetti"] == style_vars["victorian"])
solver.add(height_vars["tall"] == vacation_vars["beach"])
solver.add(height_vars["tall"] < style_vars["victorian"])
solver.add(food_vars["stir fry"] == name_vars["Bob"] - 1)
solver.add(style_vars["modern"] < name_vars["Alice"])
solver.add(style_vars["craftsman"] < height_vars["short"])
solver.add(food_vars["stir fry"] < cigar_vars["prince"])
solver.add(Abs(food_vars["grilled cheese"] - height_vars["super tall"]) == 2)
solver.add(style_vars["ranch"] == cigar_vars["blue master"])
solver.add(cigar_vars["blends"] == cigar_vars["blue master"] - 1)
solver.add(food_vars["pizza"] == vacation_vars["cultural"])
solver.add(food_vars["pizza"] < vacation_vars["cruise"])

# Check if the model is satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }
    
    for house in houses:
        name = None
        style = None
        food = None
        vacation = None
        height = None
        cigar = None
        
        for n, v in name_vars.items():
            if model[v].as_long() == house:
                name = n
                
        for s, v in style_vars.items():
            if model[v].as_long() == house:
                style = s
                
        for f, v in food_vars.items():
            if model[v].as_long() == house:
                food = f
                
        for vac, v in vacation_vars.items():
            if model[v].as_long() == house:
                vacation = vac
                
        for h, v in height_vars.items():
            if model[v].as_long() == house:
                height = h
                
        for c, v in cigar_vars.items():
            if model[v].as_long() == house:
                cigar = c
                
        solution["solution"]["rows"].append([str(house), name, style, food, vacation, height, cigar])
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")