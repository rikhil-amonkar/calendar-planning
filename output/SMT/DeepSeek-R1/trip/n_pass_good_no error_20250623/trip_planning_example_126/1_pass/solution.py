import json
from z3 import *

def main():
    # Define the city constants
    K, P, S = 0, 1, 2
    city_names = {K: "Krakow", P: "Paris", S: "Seville"}
    
    # Define the integer variables for segment boundaries and city assignments
    a = Int('a')
    b = Int('b')
    city1 = Int('city1')
    city2 = Int('city2')
    city3 = Int('city3')
    
    s = Solver()
    
    # Constraints on a and b: 1 <= a < b <= 11
    s.add(a >= 1, a <= 11, b >= 1, b <= 11, a < b)
    
    # Cities must be distinct and one of K, P, S
    s.add(Distinct(city1, city2, city3))
    s.add(Or(city1 == K, city1 == P, city1 == S))
    s.add(Or(city2 == K, city2 == P, city2 == S))
    s.add(Or(city3 == K, city3 == P, city3 == S))
    
    # Direct flight constraints between consecutive segments
    s.add(Or(
        And(city1 == K, city2 == P),
        And(city1 == P, city2 == K),
        And(city1 == P, city2 == S),
        And(city1 == S, city2 == P)
    ))
    s.add(Or(
        And(city2 == K, city3 == P),
        And(city2 == P, city3 == K),
        And(city2 == P, city3 == S),
        And(city2 == S, city3 == P)
    ))
    
    # Days in each city calculation
    days_in_K = If(city1 == K, a, 
                  If(city2 == K, (b - a + 1),
                  If(city3 == K, (11 - b + 1), 0)))
    days_in_P = If(city1 == P, a, 
                  If(city2 == P, (b - a + 1),
                  If(city3 == P, (11 - b + 1), 0)))
    days_in_S = If(city1 == S, a, 
                  If(city2 == S, (b - a + 1),
                  If(city3 == S, (11 - b + 1), 0)))
    
    s.add(days_in_K == 5)
    s.add(days_in_P == 2)
    s.add(days_in_S == 6)
    
    # Workshop constraint: at least one day in Krakow between days 1 and 5
    in_krakow_list = []
    for i in range(1, 6):
        cond = Or(
            And(city1 == K, i <= a),
            And(city2 == K, a <= i, i <= b),
            And(city3 == K, b <= i)
        )
        in_krakow_list.append(cond)
    s.add(Or(in_krakow_list))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        city1_val = m[city1].as_long()
        city2_val = m[city2].as_long()
        city3_val = m[city3].as_long()
        
        c1 = city_names[city1_val]
        c2 = city_names[city2_val]
        c3 = city_names[city3_val]
        
        itinerary = []
        
        # Segment1: Day 1 to a_val
        if a_val == 1:
            day_range1 = "Day 1"
        else:
            day_range1 = "Day 1-" + str(a_val)
        itinerary.append({"day_range": day_range1, "place": c1})
        
        # Flight day a_val: Departure from c1 and arrival to c2
        itinerary.append({"day_range": "Day " + str(a_val), "place": c1})
        itinerary.append({"day_range": "Day " + str(a_val), "place": c2})
        
        # Segment2: Day a_val to b_val
        if a_val == b_val:
            day_range2 = "Day " + str(a_val)
        else:
            day_range2 = "Day " + str(a_val) + "-" + str(b_val)
        itinerary.append({"day_range": day_range2, "place": c2})
        
        # Flight day b_val: Departure from c2 and arrival to c3
        itinerary.append({"day_range": "Day " + str(b_val), "place": c2})
        itinerary.append({"day_range": "Day " + str(b_val), "place": c3})
        
        # Segment3: Day b_val to 11
        if b_val == 11:
            day_range3 = "Day 11"
        else:
            day_range3 = "Day " + str(b_val) + "-11"
        itinerary.append({"day_range": day_range3, "place": c3})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()