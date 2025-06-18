from z3 import *
import json

def main():
    # Define the order variables for the three blocks
    order0, order1, order2 = Ints('o0 o1 o2')
    order = [order0, order1, order2]
    
    # Define block start and end variables
    bs0, be0, bs1, be1, bs2, be2 = Ints('bs0 be0 bs1 be1 bs2 be2')
    
    s = Solver()
    
    # Order constraints: each must be 0,1,2 and distinct
    s.add(Distinct(order0, order1, order2))
    s.add(order0 >= 0, order0 <= 2)
    s.add(order1 >= 0, order1 <= 2)
    s.add(order2 >= 0, order2 <= 2)
    
    # Flight connection constraints between consecutive cities
    # Allowed flights: (0,1), (1,0), (1,2), (2,1)
    s.add(Or(
        And(order0 == 0, order1 == 1),
        And(order0 == 1, order1 == 0),
        And(order0 == 1, order1 == 2),
        And(order0 == 2, order1 == 1)
    ))
    
    s.add(Or(
        And(order1 == 0, order2 == 1),
        And(order1 == 1, order2 == 0),
        And(order1 == 1, order2 == 2),
        And(order1 == 2, order2 == 1)
    ))
    
    # Days per city: Bucharest (0) -> 7, Lyon (1) -> 7, Porto (2) -> 4
    d0 = If(order0 == 0, 7, If(order0 == 1, 7, 4))
    d1 = If(order1 == 0, 7, If(order1 == 1, 7, 4))
    d2 = If(order2 == 0, 7, If(order2 == 1, 7, 4))
    
    # Block constraints
    s.add(bs0 == 1)
    s.add(be0 == bs0 + d0 - 1)
    s.add(bs1 == be0)   # next block starts on the same day the previous block ends (flight day)
    s.add(be1 == bs1 + d1 - 1)
    s.add(bs2 == be1)
    s.add(be2 == bs2 + d2 - 1)
    s.add(be2 == 16)   # the trip ends on day 16
    
    # Wedding constraint: Bucharest must start on or before day 7
    bucharest_start = If(order0 == 0, bs0, 
                         If(order1 == 0, bs1, 
                            bs2))
    s.add(bucharest_start <= 7)
    
    if s.check() == sat:
        m = s.model()
        o0_val = m[order0].as_long()
        o1_val = m[order1].as_long()
        o2_val = m[order2].as_long()
        bs0_val = m[bs0].as_long()
        be0_val = m[be0].as_long()
        bs1_val = m[bs1].as_long()
        be1_val = m[be1].as_long()
        bs2_val = m[bs2].as_long()
        be2_val = m[be2].as_long()
        
        cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
        name0 = cities[o0_val]
        name1 = cities[o1_val]
        name2 = cities[o2_val]
        
        itinerary_list = []
        
        # Block0: first city
        itinerary_list.append({"day_range": f"Day {bs0_val}-{be0_val}", "place": name0})
        itinerary_list.append({"day_range": f"Day {be0_val}", "place": name0})  # departure flight day
        
        # Block1: second city
        itinerary_list.append({"day_range": f"Day {bs1_val}", "place": name1})  # arrival flight day
        itinerary_list.append({"day_range": f"Day {bs1_val}-{be1_val}", "place": name1})
        itinerary_list.append({"day_range": f"Day {be1_val}", "place": name1})  # departure flight day
        
        # Block2: third city
        itinerary_list.append({"day_range": f"Day {bs2_val}", "place": name2})  # arrival flight day
        itinerary_list.append({"day_range": f"Day {bs2_val}-{be2_val}", "place": name2})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()