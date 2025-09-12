import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Number of houses
    n = 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Attributes
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    style_vars = [Int(f"style_{i}") for i in houses]
    food_vars = [Int(f"food_{i}") for i in houses]
    vacation_vars = [Int(f"vacation_{i}") for i in houses]
    height_vars = [Int(f"height_{i}") for i in houses]
    cigar_vars = [Int(f"cigar_{i}") for i in houses]
    
    # Domain constraints - each variable must be between 0 and 5
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < n))
        s.add(And(style_vars[i-1] >= 0, style_vars[i-1] < n))
        s.add(And(food_vars[i-1] >= 0, food_vars[i-1] < n))
        s.add(And(vacation_vars[i-1] >= 0, vacation_vars[i-1] < n))
        s.add(And(height_vars[i-1] >= 0, height_vars[i-1] < n))
        s.add(And(cigar_vars[i-1] >= 0, cigar_vars[i-1] < n))
    
    # All attributes must be distinct within their category
    s.add(Distinct(name_vars))
    s.add(Distinct(style_vars))
    s.add(Distinct(food_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(cigar_vars))
    
    # Helper functions
    def find_attr_position(attr_vars, attr_value):
        """Find the house position of an attribute value"""
        return [i+1 for i in range(n) if attr_vars[i] == attr_value][0]
    
    def get_attr_value(attr_vars, house_num):
        """Get the attribute value for a specific house"""
        return attr_vars[house_num-1]
    
    # Clue 1: Alice is in the fifth house.
    alice_idx = names.index("Alice")
    s.add(name_vars[4] == alice_idx)
    
    # Clue 2: The person who loves stir fry is the person living in a colonial-style house.
    stir_fry_idx = foods.index("stir fry")
    colonial_idx = house_styles.index("colonial")
    for i in houses:
        s.add(Implies(food_vars[i-1] == stir_fry_idx, style_vars[i-1] == colonial_idx))
    
    # Clue 3: Alice is the person who loves the spaghetti eater.
    spaghetti_idx = foods.index("spaghetti")
    s.add(food_vars[4] == spaghetti_idx)
    
    # Clue 4: Arnold is the person who loves the stew.
    arnold_idx = names.index("Arnold")
    stew_idx = foods.index("stew")
    for i in houses:
        s.add(Implies(name_vars[i-1] == arnold_idx, food_vars[i-1] == stew_idx))
    
    # Clue 5: There is one house between the person who has an average height and Peter.
    average_idx = heights.index("average")
    peter_idx = names.index("Peter")
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means positions differ by 2
                s.add(Or(
                    And(height_vars[i-1] == average_idx, name_vars[j-1] == peter_idx),
                    And(height_vars[j-1] == average_idx, name_vars[i-1] == peter_idx)
                ))
    
    # Clue 6: The person in a Craftsman-style house is not in the third house.
    craftsman_idx = house_styles.index("craftsman")
    s.add(style_vars[2] != craftsman_idx)
    
    # Clue 7: The person who has an average height is the person who loves stir fry.
    for i in houses:
        s.add(Implies(height_vars[i-1] == average_idx, food_vars[i-1] == stir_fry_idx))
    
    # Clue 8: The person who loves beach vacations is the person in a ranch-style home.
    beach_idx = vacations.index("beach")
    ranch_idx = house_styles.index("ranch")
    for i in houses:
        s.add(Implies(vacation_vars[i-1] == beach_idx, style_vars[i-1] == ranch_idx))
    
    # Clue 9: Eric is in the fourth house.
    eric_idx = names.index("Eric")
    s.add(name_vars[3] == eric_idx)
    
    # Clue 10: There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
    camping_idx = vacations.index("camping")
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means positions differ by 2
                s.add(Or(
                    And(style_vars[i-1] == colonial_idx, vacation_vars[j-1] == camping_idx),
                    And(style_vars[j-1] == colonial_idx, vacation_vars[i-1] == camping_idx)
                ))
    
    # Clue 11: The person who enjoys mountain retreats is the person who smokes Yellow Monster.
    mountain_idx = vacations.index("mountain")
    yellow_monster_idx = cigars.index("yellow monster")
    for i in houses:
        s.add(Implies(vacation_vars[i-1] == mountain_idx, cigar_vars[i-1] == yellow_monster_idx))
    
    # Clue 12: The person who enjoys mountain retreats is the person who is very tall.
    very_tall_idx = heights.index("very tall")
    for i in houses:
        s.add(Implies(vacation_vars[i-1] == mountain_idx, height_vars[i-1] == very_tall_idx))
    
    # Clue 13: The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
    dunhill_idx = cigars.index("dunhill")
    for i in houses:
        for j in houses:
            if abs(i - j) == 1:  # Adjacent houses
                s.add(Or(
                    And(vacation_vars[i-1] == mountain_idx, cigar_vars[j-1] == dunhill_idx),
                    And(vacation_vars[j-1] == mountain_idx, cigar_vars[i-1] == dunhill_idx)
                ))
    
    # Clue 14: The person who loves the spaghetti eater is the person residing in a Victorian house.
    victorian_idx = house_styles.index("victorian")
    s.add(style_vars[4] == victorian_idx)  # Alice is in 5th house and loves spaghetti eater
    
    # Clue 15: The person who is tall is the person who loves beach vacations.
    tall_idx = heights.index("tall")
    for i in houses:
        s.add(Implies(height_vars[i-1] == tall_idx, vacation_vars[i-1] == beach_idx))
    
    # Clue 16: The person who is tall is somewhere to the left of the person residing in a Victorian house.
    for i in houses:
        for j in houses:
            if i < j:  # i is left of j
                s.add(Implies(And(height_vars[i-1] == tall_idx, style_vars[j-1] == victorian_idx), i < j))
    
    # Clue 17: The person who loves stir fry is directly left of Bob.
    bob_idx = names.index("Bob")
    for i in range(1, n):
        s.add(Implies(food_vars[i-1] == stir_fry_idx, name_vars[i] == bob_idx))
    
    # Clue 18: The person in a modern-style house is somewhere to the left of Alice.
    modern_idx = house_styles.index("modern")
    for i in range(1, 5):  # Alice is in house 5, so modern must be in 1-4
        s.add(Implies(style_vars[i-1] == modern_idx, i < 5))
    
    # Clue 19: The person in a Craftsman-style house is somewhere to the left of the person who is short.
    short_idx = heights.index("short")
    for i in houses:
        for j in houses:
            if i < j:  # i is left of j
                s.add(Implies(And(style_vars[i-1] == craftsman_idx, height_vars[j-1] == short_idx), i < j))
    
    # Clue 20: The person who loves stir fry is somewhere to the left of the Prince smoker.
    prince_idx = cigars.index("prince")
    for i in houses:
        for j in houses:
            if i < j:  # i is left of j
                s.add(Implies(And(food_vars[i-1] == stir_fry_idx, cigar_vars[j-1] == prince_idx), i < j))
    
    # Clue 21: There are two houses between the person who loves eating grilled cheese and the person who is super tall.
    grilled_cheese_idx = foods.index("grilled cheese")
    super_tall_idx = heights.index("super tall")
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:  # Two houses between means positions differ by 3
                s.add(Or(
                    And(food_vars[i-1] == grilled_cheese_idx, height_vars[j-1] == super_tall_idx),
                    And(food_vars[j-1] == grilled_cheese_idx, height_vars[i-1] == super_tall_idx)
                ))
    
    # Clue 22: The person in a ranch-style home is the person who smokes Blue Master.
    blue_master_idx = cigars.index("blue master")
    for i in houses:
        s.add(Implies(style_vars[i-1] == ranch_idx, cigar_vars[i-1] == blue_master_idx))
    
    # Clue 23: The person who smokes many unique blends is directly left of the person who smokes Blue Master.
    blends_idx = cigars.index("blends")
    for i in range(1, n):
        s.add(Implies(cigar_vars[i-1] == blends_idx, cigar_vars[i] == blue_master_idx))
    
    # Clue 24: The person who goes on cultural tours is the person who is a pizza lover.
    cultural_idx = vacations.index("cultural")
    pizza_idx = foods.index("pizza")
    for i in houses:
        s.add(Implies(vacation_vars[i-1] == cultural_idx, food_vars[i-1] == pizza_idx))
    
    # Clue 25: The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
    cruise_idx = vacations.index("cruise")
    for i in houses:
        for j in houses:
            if i < j:  # i is left of j
                s.add(Implies(And(food_vars[i-1] == pizza_idx, vacation_vars[j-1] == cruise_idx), i < j))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            house_num = i + 1
            name_idx = model.evaluate(name_vars[i]).as_long()
            style_idx = model.evaluate(style_vars[i]).as_long()
            food_idx = model.evaluate(food_vars[i]).as_long()
            vacation_idx = model.evaluate(vacation_vars[i]).as_long()
            height_idx = model.evaluate(height_vars[i]).as_long()
            cigar_idx = model.evaluate(cigar_vars[i]).as_long()
            
            row = [
                str(house_num),
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