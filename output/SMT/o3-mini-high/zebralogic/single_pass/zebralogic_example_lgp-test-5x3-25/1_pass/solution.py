from z3 import *
import json

def main():
    s = Solver()

    # Define integer variables for houses for each person (names)
    xArnold, xBob, xAlice, xEric, xPeter = Ints('xArnold xBob xAlice xEric xPeter')
    names = [xArnold, xBob, xAlice, xEric, xPeter]
    for n in names:
        s.add(And(n >= 1, n <= 5))
    s.add(Distinct(xArnold, xBob, xAlice, xEric, xPeter))
    
    # Define integer variables for heights.
    # The five heights are: very short, short, average, tall, very tall.
    h_vshort, h_short, h_average, h_tall, h_vtall = Ints('h_vshort h_short h_average h_tall h_vtall')
    heights = [h_vshort, h_short, h_average, h_tall, h_vtall]
    for h in heights:
        s.add(And(h >= 1, h <= 5))
    s.add(Distinct(h_vshort, h_short, h_average, h_tall, h_vtall))
    
    # Define integer variables for foods.
    # The five foods are: stew, grilled cheese, spaghetti, pizza, stir fry.
    f_stew, f_grilled, f_spag, f_pizza, f_stir = Ints('f_stew f_grilled f_spag f_pizza f_stir')
    foods = [f_stew, f_grilled, f_spag, f_pizza, f_stir]
    for f in foods:
        s.add(And(f >= 1, f <= 5))
    s.add(Distinct(f_stew, f_grilled, f_spag, f_pizza, f_stir))
    
    # Now add the clues as constraints:
    
    # 1. Alice is the person who is short.
    s.add(xAlice == h_short)
    
    # 2. The person who is tall is in the third house.
    s.add(h_tall == 3)
    
    # 3. The person who has an average height is not in the second house.
    s.add(h_average != 2)
    
    # 4. The person who has an average height is somewhere to the left of the person who loves the stew.
    s.add(h_average < f_stew)
    
    # 5. The person who loves stir fry is Arnold.
    s.add(f_stir == xArnold)
    
    # 6. The person who is a pizza lover is the person who is tall.
    s.add(f_pizza == h_tall)
    
    # 7. Eric is the person who is tall.
    s.add(xEric == h_tall)
    
    # 8. Bob is somewhere to the right of Arnold.
    s.add(xBob > xArnold)
    
    # 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
    s.add(f_grilled > xEric)
    
    # 10. The person who is very short is somewhere to the left of Arnold.
    s.add(h_vshort < xArnold)
    
    # Solve constraints
    if s.check() == sat:
        m = s.model()
        
        # Build mappings from attribute to house number results
        solution_names = {
            "Arnold": m[xArnold].as_long(),
            "Bob": m[xBob].as_long(),
            "Alice": m[xAlice].as_long(),
            "Eric": m[xEric].as_long(),
            "Peter": m[xPeter].as_long()
        }
        
        solution_heights = {
            "very short": m[h_vshort].as_long(),
            "short": m[h_short].as_long(),
            "average": m[h_average].as_long(),
            "tall": m[h_tall].as_long(),
            "very tall": m[h_vtall].as_long()
        }
        
        solution_foods = {
            "stew": m[f_stew].as_long(),
            "grilled cheese": m[f_grilled].as_long(),
            "spaghetti": m[f_spag].as_long(),
            "pizza": m[f_pizza].as_long(),
            "stir fry": m[f_stir].as_long()
        }
        
        # Invert the mappings: for each house 1..5, determine which Name, Height, and Food is there.
        name_by_house = {}
        for person, pos in solution_names.items():
            name_by_house[pos] = person
            
        height_by_house = {}
        for ht, pos in solution_heights.items():
            height_by_house[pos] = ht
            
        food_by_house = {}
        for food, pos in solution_foods.items():
            food_by_house[pos] = food
        
        # Prepare rows for houses 1 to 5 (houses are numbered left to right)
        rows = []
        for house_num in range(1, 6):
            row = [
                str(house_num),
                name_by_house.get(house_num, ""),
                height_by_house.get(house_num, ""),
                food_by_house.get(house_num, "")
            ]
            rows.append(row)
        
        # Build final JSON structure
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()