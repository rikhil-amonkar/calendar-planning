import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Number of houses
    n = 6
    houses = list(range(n))  # Use 0-indexed internally
    
    # Attributes
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in range(n)]
    style_vars = [Int(f"style_{i}") for i in range(n)]
    food_vars = [Int(f"food_{i}") for i in range(n)]
    vacation_vars = [Int(f"vacation_{i}") for i in range(n)]
    height_vars = [Int(f"height_{i}") for i in range(n)]
    cigar_vars = [Int(f"cigar_{i}") for i in range(n)]
    
    # Domain constraints - each variable must be between 0 and 5
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < n))
        s.add(And(style_vars[i] >= 0, style_vars[i] < n))
        s.add(And(food_vars[i] >= 0, food_vars[i] < n))
        s.add(And(vacation_vars[i] >= 0, vacation_vars[i] < n))
        s.add(And(height_vars[i] >= 0, height_vars[i] < n))
        s.add(And(cigar_vars[i] >= 0, cigar_vars[i] < n))
    
    # All attributes must be distinct within their category
    s.add(Distinct(name_vars))
    s.add(Distinct(style_vars))
    s.add(Distinct(food_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(cigar_vars))
    
    # Get index values
    alice_idx = names.index("Alice")
    arnold_idx = names.index("Arnold")
    peter_idx = names.index("Peter")
    eric_idx = names.index("Eric")
    bob_idx = names.index("Bob")
    
    ranch_idx = house_styles.index("ranch")
    colonial_idx = house_styles.index("colonial")
    modern_idx = house_styles.index("modern")
    craftsman_idx = house_styles.index("craftsman")
    victorian_idx = house_styles.index("victorian")
    
    pizza_idx = foods.index("pizza")
    stew_idx = foods.index("stew")
    spaghetti_idx = foods.index("spaghetti")
    grilled_cheese_idx = foods.index("grilled cheese")
    stir_fry_idx = foods.index("stir fry")
    soup_idx = foods.index("soup")
    
    cultural_idx = vacations.index("cultural")
    cruise_idx = vacations.index("cruise")
    mountain_idx = vacations.index("mountain")
    camping_idx = vacations.index("camping")
    beach_idx = vacations.index("beach")
    
    average_idx = heights.index("average")
    very_tall_idx = heights.index("very tall")
    very_short_idx = heights.index("very short")
    short_idx = heights.index("short")
    tall_idx = heights.index("tall")
    super_tall_idx = heights.index("super tall")
    
    yellow_monster_idx = cigars.index("yellow monster")
    prince_idx = cigars.index("prince")
    dunhill_idx = cigars.index("dunhill")
    pall_mall_idx = cigars.index("pall mall")
    blue_master_idx = cigars.index("blue master")
    blends_idx = cigars.index("blends")
    
    # Clue 1: Alice is in the fifth house.
    s.add(name_vars[4] == alice_idx)
    
    # Clue 2: The person who loves stir fry is the person living in a colonial-style house.
    for i in range(n):
        s.add(Implies(food_vars[i] == stir_fry_idx, style_vars[i] == colonial_idx))
    
    # Clue 3: Alice is the person who loves the spaghetti eater.
    s.add(food_vars[4] == spaghetti_idx)
    
    # Clue 4: Arnold is the person who loves the stew.
    for i in range(n):
        s.add(Implies(name_vars[i] == arnold_idx, food_vars[i] == stew_idx))
    
    # Clue 5: There is one house between the person who has an average height and Peter.
    average_height_pos = Int("average_height_pos")
    peter_pos = Int("peter_pos")
    s.add(average_height_pos >= 0, average_height_pos < n)
    s.add(peter_pos >= 0, peter_pos < n)
    
    for i in range(n):
        s.add(Implies(height_vars[i] == average_idx, average_height_pos == i))
        s.add(Implies(name_vars[i] == peter_idx, peter_pos == i))
    
    s.add(Or(
        average_height_pos == peter_pos + 2,
        average_height_pos == peter_pos - 2
    ))
    
    # Clue 6: The person in a Craftsman-style house is not in the third house.
    s.add(style_vars[2] != craftsman_idx)
    
    # Clue 7: The person who has an average height is the person who loves stir fry.
    for i in range(n):
        s.add(Implies(height_vars[i] == average_idx, food_vars[i] == stir_fry_idx))
    
    # Clue 8: The person who loves beach vacations is the person in a ranch-style home.
    for i in range(n):
        s.add(Implies(vacation_vars[i] == beach_idx, style_vars[i] == ranch_idx))
    
    # Clue 9: Eric is in the fourth house.
    s.add(name_vars[3] == eric_idx)
    
    # Clue 10: There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
    colonial_pos = Int("colonial_pos")
    camping_pos = Int("camping_pos")
    s.add(colonial_pos >= 0, colonial_pos < n)
    s.add(camping_pos >= 0, camping_pos < n)
    
    for i in range(n):
        s.add(Implies(style_vars[i] == colonial_idx, colonial_pos == i))
        s.add(Implies(vacation_vars[i] == camping_idx, camping_pos == i))
    
    s.add(Or(
        colonial_pos == camping_pos + 2,
        colonial_pos == camping_pos - 2
    ))
    
    # Clue 11: The person who enjoys mountain retreats is the person who smokes Yellow Monster.
    for i in range(n):
        s.add(Implies(vacation_vars[i] == mountain_idx, cigar_vars[i] == yellow_monster_idx))
    
    # Clue 12: The person who enjoys mountain retreats is the person who is very tall.
    for i in range(n):
        s.add(Implies(vacation_vars[i] == mountain_idx, height_vars[i] == very_tall_idx))
    
    # Clue 13: The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
    mountain_pos = Int("mountain_pos")
    dunhill_pos = Int("dunhill_pos")
    s.add(mountain_pos >= 0, mountain_pos < n)
    s.add(dunhill_pos >= 0, dunhill_pos < n)
    
    for i in range(n):
        s.add(Implies(vacation_vars[i] == mountain_idx, mountain_pos == i))
        s.add(Implies(cigar_vars[i] == dunhill_idx, dunhill_pos == i))
    
    s.add(Or(
        mountain_pos == dunhill_pos + 1,
        mountain_pos == dunhill_pos - 1
    ))
    
    # Clue 14: The person who loves the spaghetti eater is the person residing in a Victorian house.
    s.add(style_vars[4] == victorian_idx)  # Alice is in 5th house and loves spaghetti
    
    # Clue 15: The person who is tall is the person who loves beach vacations.
    for i in range(n):
        s.add(Implies(height_vars[i] == tall_idx, vacation_vars[i] == beach_idx))
    
    # Clue 16: The person who is tall is somewhere to the left of the person residing in a Victorian house.
    tall_pos = Int("tall_pos")
    victorian_pos = Int("victorian_pos")
    s.add(tall_pos >= 0, tall_pos < n)
    s.add(victorian_pos >= 0, victorian_pos < n)
    
    for i in range(n):
        s.add(Implies(height_vars[i] == tall_idx, tall_pos == i))
        s.add(Implies(style_vars[i] == victorian_idx, victorian_pos == i))
    
    s.add(tall_pos < victorian_pos)
    
    # Clue 17: The person who loves stir fry is directly left of Bob.
    stir_fry_pos = Int("stir_fry_pos")
    bob_pos = Int("bob_pos")
    s.add(stir_fry_pos >= 0, stir_fry_pos < n)
    s.add(bob_pos >= 0, bob_pos < n)
    
    for i in range(n):
        s.add(Implies(food_vars[i] == stir_fry_idx, stir_fry_pos == i))
        s.add(Implies(name_vars[i] == bob_idx, bob_pos == i))
    
    s.add(stir_fry_pos + 1 == bob_pos)
    
    # Clue 18: The person in a modern-style house is somewhere to the left of Alice.
    modern_pos = Int("modern_pos")
    s.add(modern_pos >= 0, modern_pos < n)
    
    for i in range(n):
        s.add(Implies(style_vars[i] == modern_idx, modern_pos == i))
    
    s.add(modern_pos < 4)  # Alice is in position 4 (0-indexed)
    
    # Clue 19: The person in a Craftsman-style house is somewhere to the left of the person who is short.
    craftsman_pos = Int("craftsman_pos")
    short_pos = Int("short_pos")
    s.add(craftsman_pos >= 0, craftsman_pos < n)
    s.add(short_pos >= 0, short_pos < n)
    
    for i in range(n):
        s.add(Implies(style_vars[i] == craftsman_idx, craftsman_pos == i))
        s.add(Implies(height_vars[i] == short_idx, short_pos == i))
    
    s.add(craftsman_pos < short_pos)
    
    # Clue 20: The person who loves stir fry is somewhere to the left of the Prince smoker.
    prince_pos = Int("prince_pos")
    s.add(prince_pos >= 0, prince_pos < n)
    
    for i in range(n):
        s.add(Implies(cigar_vars[i] == prince_idx, prince_pos == i))
    
    s.add(stir_fry_pos < prince_pos)
    
    # Clue 21: There are two houses between the person who loves eating grilled cheese and the person who is super tall.
    grilled_cheese_pos = Int("grilled_cheese_pos")
    super_tall_pos = Int("super_tall_pos")
    s.add(grilled_cheese_pos >= 0, grilled_cheese_pos < n)
    s.add(super_tall_pos >= 0, super_tall_pos < n)
    
    for i in range(n):
        s.add(Implies(food_vars[i] == grilled_cheese_idx, grilled_cheese_pos == i))
        s.add(Implies(height_vars[i] == super_tall_idx, super_tall_pos == i))
    
    s.add(Or(
        grilled_cheese_pos == super_tall_pos + 3,
        grilled_cheese_pos == super_tall_pos - 3
    ))
    
    # Clue 22: The person in a ranch-style home is the person who smokes Blue Master.
    for i in range(n):
        s.add(Implies(style_vars[i] == ranch_idx, cigar_vars[i] == blue_master_idx))
    
    # Clue 23: The person who smokes many unique blends is directly left of the person who smokes Blue Master.
    blends_pos = Int("blends_pos")
    blue_master_pos = Int("blue_master_pos")
    s.add(blends_pos >= 0, blends_pos < n)
    s.add(blue_master_pos >= 0, blue_master_pos < n)
    
    for i in range(n):
        s.add(Implies(cigar_vars[i] == blends_idx, blends_pos == i))
        s.add(Implies(cigar_vars[i] == blue_master_idx, blue_master_pos == i))
    
    s.add(blends_pos + 1 == blue_master_pos)
    
    # Clue 24: The person who goes on cultural tours is the person who is a pizza lover.
    for i in range(n):
        s.add(Implies(vacation_vars[i] == cultural_idx, food_vars[i] == pizza_idx))
    
    # Clue 25: The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
    pizza_pos = Int("pizza_pos")
    cruise_pos = Int("cruise_pos")
    s.add(pizza_pos >= 0, pizza_pos < n)
    s.add(cruise_pos >= 0, cruise_pos < n)
    
    for i in range(n):
        s.add(Implies(food_vars[i] == pizza_idx, pizza_pos == i))
        s.add(Implies(vacation_vars[i] == cruise_idx, cruise_pos == i))
    
    s.add(pizza_pos < cruise_pos)
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            name_idx = model.evaluate(name_vars[i]).as_long()
            style_idx = model.evaluate(style_vars[i]).as_long()
            food_idx = model.evaluate(food_vars[i]).as_long()
            vacation_idx = model.evaluate(vacation_vars[i]).as_long()
            height_idx = model.evaluate(height_vars[i]).as_long()
            cigar_idx = model.evaluate(cigar_vars[i]).as_long()
            
            row = [
                str(i + 1),
                names[name_idx],
                house_styles[style_idx],
                foods[food_idx],
                vacations[vacation_idx],
                heights[height_idx],
                cigars[cigar_idx]
            ]
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()