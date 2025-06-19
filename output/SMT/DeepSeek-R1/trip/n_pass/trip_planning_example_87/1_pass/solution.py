from z3 import *
import json

def main():
    # Define the city enum
    City, (c_Riga, c_Amsterdam, c_Mykonos) = EnumSort('City', ['Riga', 'Amsterdam', 'Mykonos'])
    city_names = {
        c_Riga: "Riga",
        c_Amsterdam: "Amsterdam",
        c_Mykonos: "Mykonos"
    }
    
    # Define the flight days and order
    f1 = Int('f1')
    f2 = Int('f2')
    order = [Const(f'order_{i}', City) for i in range(3)]
    
    s = Solver()
    
    # Constraints on flight days
    s.add(f1 >= 1, f1 <= 6)
    s.add(f2 >= 2, f2 <= 7)
    s.add(f1 < f2)
    
    # Segment lengths
    seg0 = f1
    seg1 = f2 - f1 + 1
    seg2 = 8 - f2   # because 7 - f2 + 1 = 8 - f2
    
    # The three segments must be permutations of [2, 2, 5]
    s.add(Or(
        And(seg0 == 2, seg1 == 2, seg2 == 5),
        And(seg0 == 2, seg1 == 5, seg2 == 2),
        And(seg0 == 5, seg1 == 2, seg2 == 2)
    ))
    
    # Each city appears exactly once
    s.add(Distinct(order[0], order[1], order[2]))
    
    # The direct flight constraints for adjacent segments
    direct_pairs = [
        (c_Riga, c_Amsterdam),
        (c_Amsterdam, c_Riga),
        (c_Amsterdam, c_Mykonos),
        (c_Mykonos, c_Amsterdam)
    ]
    s.add(Or([And(order[0] == pair[0], order[1] == pair[1]) for pair in direct_pairs]))
    s.add(Or([And(order[1] == pair[0], order[2] == pair[1]) for pair in direct_pairs]))
    
    # Constraints on the days per city
    # Riga: 2 days
    s.add(Implies(order[0] == c_Riga, seg0 == 2))
    s.add(Implies(order[1] == c_Riga, seg1 == 2))
    s.add(Implies(order[2] == c_Riga, seg2 == 2))
    
    # Amsterdam: 2 days
    s.add(Implies(order[0] == c_Amsterdam, seg0 == 2))
    s.add(Implies(order[1] == c_Amsterdam, seg1 == 2))
    s.add(Implies(order[2] == c_Amsterdam, seg2 == 2))
    
    # Mykonos: 5 days
    s.add(Implies(order[0] == c_Mykonos, seg0 == 5))
    s.add(Implies(order[1] == c_Mykonos, seg1 == 5))
    s.add(Implies(order[2] == c_Mykonos, seg2 == 5))
    
    # Riga relative visit: must be in Riga on day1 or day2.
    s.add(Or(
        order[0] == c_Riga,
        And(order[1] == c_Riga, f1 <= 2),
        And(order[2] == c_Riga, f2 <= 2)
    ))
    
    if s.check() == sat:
        m = s.model()
        f1_val = m[f1].as_long()
        f2_val = m[f2].as_long()
        order_vals = [m[o] for o in order]
        city0 = city_names[order_vals[0]]
        city1 = city_names[order_vals[1]]
        city2 = city_names[order_vals[2]]
        
        itinerary = []
        
        # Segment0: from day1 to f1_val (inclusive)
        if f1_val == 1:
            itinerary.append({"day_range": "Day 1", "place": city0})
        else:
            itinerary.append({"day_range": f"Day 1-{f1_val}", "place": city0})
        
        # Flight on f1_val: from city0 to city1
        itinerary.append({"day_range": f"Day {f1_val}", "place": city0})
        itinerary.append({"day_range": f"Day {f1_val}", "place": city1})
        
        # Segment1: from f1_val to f2_val (inclusive)
        if f1_val == f2_val:
            itinerary.append({"day_range": f"Day {f1_val}", "place": city1})
        else:
            itinerary.append({"day_range": f"Day {f1_val}-{f2_val}", "place": city1})
        
        # Flight on f2_val: from city1 to city2
        itinerary.append({"day_range": f"Day {f2_val}", "place": city1})
        itinerary.append({"day_range": f"Day {f2_val}", "place": city2})
        
        # Segment2: from f2_val to day7
        if f2_val == 7:
            itinerary.append({"day_range": "Day 7", "place": city2})
        else:
            itinerary.append({"day_range": f"Day {f2_val}-7", "place": city2})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()