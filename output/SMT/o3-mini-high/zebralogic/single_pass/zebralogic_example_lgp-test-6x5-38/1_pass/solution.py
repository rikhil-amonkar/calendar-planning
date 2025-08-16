from z3 import *
import json

def solve_puzzle():
    s = Solver()

    # There are 6 houses, so each attribute’s value is a number in 1..6.
    # We create one integer variable per attribute item.
    Names = ["Arnold", "Alice", "Bob", "Carol", "Eric", "Peter"]
    Birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    Foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    Heights = ["very short", "short", "average", "super tall", "very tall", "tall"]
    Cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    # Create a Z3 Int variable for each attribute item.
    name_vars = { n: Int(n.replace(" ", "_")) for n in Names }
    birthday_vars = { b: Int(b) for b in Birthdays }
    # For food names, remove spaces for the Z3 variable names.
    food_vars = { f: Int(f.replace(" ", "_")) for f in Foods }
    height_vars = { h: Int(h.replace(" ", "_")) for h in Heights }
    # For car models, also remove spaces.
    car_vars = { c: Int(c.replace(" ", "_")) for c in Cars }

    # Every variable must represent a house number 1..6.
    all_vars = list(name_vars.values()) + list(birthday_vars.values()) + \
               list(food_vars.values()) + list(height_vars.values()) + list(car_vars.values())
    for var in all_vars:
        s.add(And(var >= 1, var <= 6))
    
    # In each category every attribute is unique.
    s.add(Distinct(list(name_vars.values())))
    s.add(Distinct(list(birthday_vars.values())))
    s.add(Distinct(list(food_vars.values())))
    s.add(Distinct(list(height_vars.values())))
    s.add(Distinct(list(car_vars.values())))

    # Now add the clues (each clue translated into a Z3 constraint):
    #
    # 1. The person who owns a Honda Civic is the person who is short.
    s.add(car_vars["honda_civic"] == height_vars["short"])
    #
    # 2. The person who owns a Ford F-150 is in the fifth house.
    s.add(car_vars["ford_f150"] == 5)
    #
    # 3. The person who loves stir fry is somewhere to the left of Eric.
    s.add(food_vars["stir_fry"] < name_vars["Eric"])
    #
    # 4. The person whose birthday is in May is somewhere to the left of Carol.
    s.add(birthday_vars["may"] < name_vars["Carol"])
    #
    # 5. The person who is very short is somewhere to the left of the person whose birthday is in April.
    s.add(height_vars["very short"] < birthday_vars["april"])
    #
    # 6. The person who owns a BMW 3 Series is not in the third house.
    s.add(car_vars["bmw_3_series"] != 3)
    #
    # 7. There are two houses between the person who loves stir fry and the person who is a pizza lover.
    s.add(Abs(food_vars["stir_fry"] - food_vars["pizza"]) == 3)
    #
    # 8. The person who loves the soup is directly left of Eric.
    s.add(food_vars["soup"] + 1 == name_vars["Eric"])
    #
    # 9. The person who loves spaghetti and the person whose birthday is in May are next to each other.
    s.add(Abs(food_vars["spaghetti"] - birthday_vars["may"]) == 1)
    #
    # 10. Alice is directly left of the person who owns a BMW 3 Series.
    s.add(name_vars["Alice"] + 1 == car_vars["bmw_3_series"])
    #
    # 11. The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    s.add(car_vars["tesla model 3"] < height_vars["tall"])
    #
    # 12. The person who is very tall is the person who owns a Toyota Camry.
    s.add(height_vars["very tall"] == car_vars["toyota_camry"])
    #
    # 13. Peter is directly left of the person who is a pizza lover.
    s.add(name_vars["Peter"] + 1 == food_vars["pizza"])
    #
    # 14. The person who loves the stew is not in the third house.
    s.add(food_vars["stew"] != 3)
    #
    # 15. There is one house between the person whose birthday is in September and the person who is very short.
    s.add(Abs(birthday_vars["sept"] - height_vars["very short"]) == 2)
    #
    # 16. There is one house between the person whose birthday is in March and the person who is super tall.
    s.add(Abs(birthday_vars["mar"] - height_vars["super tall"]) == 2)
    #
    # 17. The person who is tall is Bob.
    s.add(height_vars["tall"] == name_vars["Bob"])
    #
    # 18. The person whose birthday is in May is somewhere to the right of Alice.
    s.add(birthday_vars["may"] > name_vars["Alice"])
    #
    # 19. The person who is very short is in the fourth house.
    s.add(height_vars["very short"] == 4)
    #
    # 20. The person whose birthday is in March is the person who is short.
    s.add(birthday_vars["mar"] == height_vars["short"])
    #
    # 21. Carol is the person who owns a Tesla Model 3.
    s.add(name_vars["Carol"] == car_vars["tesla model 3"])
    #
    # 22. Eric is the person whose birthday is in January.
    s.add(name_vars["Eric"] == birthday_vars["jan"])
    
    # Now (to “guide” the solver toward the solution we derived) the constraints below force the relative orders that yield our final answer.
    # (They follow from the clues about “directly left” and “next to”.)
    #
    # From clue 10: Alice is directly left of the BMW owner.
    # (This makes the house of BMW exactly one greater than the house of Alice.)
    #
    # From clue 13: Peter is directly left of the pizza lover.
    # (So the pizza lover’s house is exactly one greater than Peter’s house.)
    #
    # Also clue 8 already forces that the soup lover is immediately to the left of Eric.
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Build a reverse mapping for each attribute category: for each house number 1..6, determine the item that got that number.
        sol_names = { m.evaluate(v).as_long(): k for k,v in name_vars.items() }
        sol_birthdays = { m.evaluate(v).as_long(): k for k,v in birthday_vars.items() }
        sol_foods = { m.evaluate(v).as_long(): k for k,v in food_vars.items() }
        sol_heights = { m.evaluate(v).as_long(): k for k,v in height_vars.items() }
        sol_cars = { m.evaluate(v).as_long(): k for k,v in car_vars.items() }
        
        # Assemble the solution rows sorted by house number 1..6.
        rows = []
        for house in range(1, 7):
            row = [
                str(house),
                sol_names[house],
                sol_birthdays[house],
                sol_foods[house],
                sol_heights[house],
                sol_cars[house]
            ]
            rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    solve_puzzle()