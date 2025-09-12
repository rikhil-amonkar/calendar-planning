from z3 import *
import json

def main():
    solver = Solver()
    
    # Define the houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Peter']
    vacations = ['mountain', 'city', 'beach']
    heights = ['very short', 'short', 'average']
    flowers = ['carnations', 'daffodils', 'lilies']
    hair_colors = ['brown', 'black', 'blonde']
    educations = ['associate', 'bachelor', 'high school']
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{h}") for h in houses]
    vacation_vars = [Int(f"vacation_{h}") for h in houses]
    height_vars = [Int(f"height_{h}") for h in houses]
    flower_vars = [Int(f"flower_{h}") for h in houses]
    hair_color_vars = [Int(f"hair_color_{h}") for h in houses]
    education_vars = [Int(f"education_{h}") for h in houses]
    
    # Each attribute must be between 0 and 2 (representing the index in the attribute list)
    for h in houses:
        solver.add(And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(And(vacation_vars[h-1] >= 0, vacation_vars[h-1] < len(vacations)))
        solver.add(And(height_vars[h-1] >= 0, height_vars[h-1] < len(heights)))
        solver.add(And(flower_vars[h-1] >= 0, flower_vars[h-1] < len(flowers)))
        solver.add(And(hair_color_vars[h-1] >= 0, hair_color_vars[h-1] < len(hair_colors)))
        solver.add(And(education_vars[h-1] >= 0, education_vars[h-1] < len(educations)))
    
    # All attributes are distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(vacation_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(flower_vars))
    solver.add(Distinct(hair_color_vars))
    solver.add(Distinct(education_vars))
    
    # Clue 1: Peter is the person who has an average height.
    # Peter is at index 2 in names, average height is at index 2 in heights
    for h in houses:
        solver.add(Implies(name_vars[h-1] == 2, height_vars[h-1] == 2))
    
    # Clue 2: The person who loves a bouquet of daffodils is Arnold.
    # Arnold is at index 1 in names, daffodils is at index 1 in flowers
    for h in houses:
        solver.add(Implies(flower_vars[h-1] == 1, name_vars[h-1] == 1))
    
    # Clue 3: The person who is very short is not in the second house.
    # very short is at index 0 in heights
    solver.add(height_vars[1] != 0)
    
    # Clue 4: The person who loves beach vacations is in the first house.
    # beach is at index 2 in vacations
    solver.add(vacation_vars[0] == 2)
    
    # Clue 5: The person with a high school diploma is in the third house.
    # high school is at index 2 in educations
    solver.add(education_vars[2] == 2)
    
    # Clue 6: The person who is short is somewhere to the right of the person who is very short.
    # short is at index 1, very short is at index 0 in heights
    very_short_house = Int("very_short_house")
    short_house = Int("short_house")
    solver.add(very_short_house >= 1, very_short_house <= 3)
    solver.add(short_house >= 1, short_house <= 3)
    
    for h in houses:
        solver.add(Implies(height_vars[h-1] == 0, very_short_house == h))
        solver.add(Implies(height_vars[h-1] == 1, short_house == h))
    
    solver.add(short_house > very_short_house)
    
    # Clue 7: The person who loves the bouquet of lilies is Eric.
    # Eric is at index 0 in names, lilies is at index 2 in flowers
    for h in houses:
        solver.add(Implies(flower_vars[h-1] == 2, name_vars[h-1] == 0))
    
    # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
    # lilies is at index 2 in flowers, bachelor is at index 1 in educations
    for h in houses:
        solver.add(Implies(flower_vars[h-1] == 2, education_vars[h-1] == 1))
    
    # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
    # city is at index 1 in vacations, Peter is at index 2 in names
    peter_house = Int("peter_house")
    city_house = Int("city_house")
    solver.add(peter_house >= 1, peter_house <= 3)
    solver.add(city_house >= 1, city_house <= 3)
    
    for h in houses:
        solver.add(Implies(name_vars[h-1] == 2, peter_house == h))
        solver.add(Implies(vacation_vars[h-1] == 1, city_house == h))
    
    solver.add(city_house > peter_house)
    
    # Clue 10: The person who has blonde hair is in the third house.
    # blonde is at index 2 in hair_colors
    solver.add(hair_color_vars[2] == 2)
    
    # Clue 11: The person who loves beach vacations is the person who has brown hair.
    # beach is at index 2 in vacations, brown is at index 0 in hair_colors
    for h in houses:
        solver.add(Implies(vacation_vars[h-1] == 2, hair_color_vars[h-1] == 0))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            vacation_idx = model.evaluate(vacation_vars[h-1]).as_long()
            height_idx = model.evaluate(height_vars[h-1]).as_long()
            flower_idx = model.evaluate(flower_vars[h-1]).as_long()
            hair_color_idx = model.evaluate(hair_color_vars[h-1]).as_long()
            education_idx = model.evaluate(education_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                vacations[vacation_idx],
                heights[height_idx],
                flowers[flower_idx],
                hair_colors[hair_color_idx],
                educations[education_idx]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()