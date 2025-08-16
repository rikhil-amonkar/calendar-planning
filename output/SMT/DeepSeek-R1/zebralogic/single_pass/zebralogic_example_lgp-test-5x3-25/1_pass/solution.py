from z3 import *

def main():
    # Define the sorts for names, heights, and foods
    NameSort, (Arnold, Bob, Alice, Eric, Peter) = EnumSort('NameSort', ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter'])
    HeightSort, (very_tall, average, tall, very_short, short) = EnumSort('HeightSort', ['very tall', 'average', 'tall', 'very short', 'short'])
    FoodSort, (stew, grilled_cheese, spaghetti, pizza, stir_fry) = EnumSort('FoodSort', ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry'])
    
    # Create variables for each house: 0-indexed for houses 1 to 5
    n = [Const('n%d' % i, NameSort) for i in range(5)]
    h = [Const('h%d' % i, HeightSort) for i in range(5)]
    f = [Const('f%d' % i, FoodSort) for i in range(5)]
    
    s = Solver()
    
    # Each attribute list must be distinct
    s.add(Distinct(n))
    s.add(Distinct(h))
    s.add(Distinct(f))
    
    # Clue 2: The person who is tall is in the third house (index 2)
    s.add(h[2] == tall)
    # Clue 7: Eric is the person who is tall -> so Eric in third house
    s.add(n[2] == Eric)
    # Clue 6: The person who loves pizza is the person who is tall -> pizza in third house
    s.add(f[2] == pizza)
    
    # Clue 1: Alice is the person who is short
    for i in range(5):
        s.add( (n[i] == Alice) == (h[i] == short) )
    
    # Clue 3: The person who has an average height is not in the second house (index1)
    s.add(h[1] != average)
    
    # Clue 4: The person who has an average height is somewhere to the left of the person who loves the stew.
    for i in range(5):
        for j in range(5):
            s.add(Implies(And(h[i] == average, f[j] == stew), i < j)
    
    # Clue 5: The person who loves stir fry is Arnold.
    for i in range(5):
        s.add( (f[i] == stir_fry) == (n[i] == Arnold) )
    
    # Clue 8: Bob is somewhere to the right of Arnold.
    for i in range(5):
        for j in range(5):
            s.add(Implies(And(n[i] == Arnold, n[j] == Bob), i < j)
    
    # Clue 9: The person who loves grilled cheese is somewhere to the right of Eric (who is in house index2).
    for i in range(5):
        s.add(Implies(f[i] == grilled_cheese, i > 2))
    
    # Clue 10: The person who is very short is somewhere to the left of Arnold.
    for i in range(5):
        for j in range(5):
            s.add(Implies(And(h[i] == very_short, n[j] == Arnold), i < j)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract the values for each house
        result = []
        for i in range(5):
            house_num = i+1
            name_val = model.eval(n[i])
            height_val = model.eval(h[i])
            food_val = model.eval(f[i])
            # Convert the Z3 constants to string names
            name_str = ('Arnold' if name_val == Arnold else 
                        'Bob' if name_val == Bob else 
                        'Alice' if name_val == Alice else 
                        'Eric' if name_val == Eric else 
                        'Peter')
            height_str = ('very tall' if height_val == very_tall else 
                          'average' if height_val == average else 
                          'tall' if height_val == tall else 
                          'very short' if height_val == very_short else 
                          'short')
            food_str = ('stew' if food_val == stew else 
                        'grilled cheese' if food_val == grilled_cheese else 
                        'spaghetti' if food_val == spaghetti else 
                        'pizza' if food_val == pizza else 
                        'stir fry')
            result.append([str(house_num), name_str, height_str, food_str])
        
        # Format the output as JSON
        json_output = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": result
            }
        }
        import json
        print(json.dumps(json_output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()