import json
from z3 import *

def main():
    # Required days for each city
    req_days = {
        'Warsaw': 2,
        'Budapest': 7,
        'Paris': 4,
        'Riga': 7
    }
    
    # City mapping
    cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
    city_dict = {c: i for i, c in enumerate(cities)}
    
    # Direct flights: graph represented as adjacency list
    direct_flights = {
        0: [1, 2, 3],  # Warsaw
        1: [0, 2],      # Budapest
        2: [0, 1, 3],   # Paris
        3: [0, 2]       # Riga
    }
    
    # Create solver
    s = Solver()
    
    # Flight days: a, b, c
    a = Int('a')
    b = Int('b')
    c = Int('c')
    
    # Segment cities
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    
    # Constraints on flight days
    s.add(a == 2)  # Warsaw must have 2 days
    s.add(a >= 1, a <= 16)
    s.add(b > a, b <= 16)
    s.add(c > b, c <= 16)
    
    # All segments are distinct and not Warsaw (0)
    s.add(Distinct(s2, s3, s4))
    s.add(s2 >= 1, s2 <= 3)
    s.add(s3 >= 1, s3 <= 3)
    s.add(s4 >= 1, s4 <= 3)
    
    # Direct flight constraints
    s.add(Or([s2 == city for city in direct_flights[0]]))
    s.add(Or([s3 == city for city in direct_flights[s2]]))
    s.add(Or([s4 == city for city in direct_flights[s3]]))
    
    # Duration constraints for segments
    s.add(If(s2 == city_dict['Budapest'], b - a + 1 == req_days['Budapest'],
          If(s2 == city_dict['Paris'], b - a + 1 == req_days['Paris'],
          If(s2 == city_dict['Riga'], b - a + 1 == req_days['Riga'], False))))
    
    s.add(If(s3 == city_dict['Budapest'], c - b + 1 == req_days['Budapest'],
          If(s3 == city_dict['Paris'], c - b + 1 == req_days['Paris'],
          If(s3 == city_dict['Riga'], c - b + 1 == req_days['Riga'], False))))
    
    s.add(If(s4 == city_dict['Budapest'], 17 - c + 1 == req_days['Budapest'],
          If(s4 == city_dict['Paris'], 17 - c + 1 == req_days['Paris'],
          If(s4 == city_dict['Riga'], 17 - c + 1 == req_days['Riga'], False))))
    
    # Wedding constraint: must be in Riga between day 11 and 17
    s.add(Or(
        And(s2 == city_dict['Riga'], b >= 11),
        And(s3 == city_dict['Riga'], b <= 11, c >= 11),
        And(s4 == city_dict['Riga'], c <= 11)
    ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        c_val = m[c].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        s4_val = m[s4].as_long()
        
        # Map segment indices to city names
        seg1_city = cities[0]
        seg2_city = cities[s2_val]
        seg3_city = cities[s3_val]
        seg4_city = cities[s4_val]
        
        # Create itinerary segments
        itinerary = [
            {"day_range": f"Day 1-{a_val}", "place": seg1_city},
            {"day_range": f"Day {a_val}-{b_val}", "place": seg2_city},
            {"day_range": f"Day {b_val}-{c_val}", "place": seg3_city},
            {"day_range": f"Day {c_val}-17", "place": seg4_city}
        ]
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()