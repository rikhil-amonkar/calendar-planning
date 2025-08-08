from z3 import *
import json

def main():
    # Define the integer variables for the segment boundaries
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    
    # Define the city variables for each segment (0: Seville, 1: Stuttgart, 2: Porto, 3: Madrid)
    C1 = Int('C1')
    C2 = Int('C2')
    C3 = Int('C3')
    C4 = Int('C4')
    
    s = Solver()
    
    # Boundaries: 1 <= d1 <= d2 <= d3 <= 13
    s.add(And(1 <= d1, d1 <= d2, d2 <= d3, d3 <= 13))
    
    # Each city variable must be in {0,1,2,3}
    s.add(And(C1 >= 0, C1 <= 3))
    s.add(And(C2 >= 0, C2 <= 3))
    s.add(And(C3 >= 0, C3 <= 3))
    s.add(And(C4 >= 0, C4 <= 3))
    
    # Define the direct flight edges (undirected)
    edges = [(0,2), (0,3), (1,2), (2,3)]  # (Seville,Porto), (Seville,Madrid), (Stuttgart,Porto), (Porto,Madrid)
    
    def flight_ok(c1, c2):
        options = []
        for (a,b) in edges:
            options.append(And(c1 == a, c2 == b))
            options.append(And(c1 == b, c2 == a))
        return Or(options)
    
    # Flight constraints between consecutive segments
    s.add(flight_ok(C1, C2))
    s.add(flight_ok(C2, C3))
    s.add(flight_ok(C3, C4))
    
    # Total days per city: Seville (0), Stuttgart (1), Porto (2), Madrid (3)
    total_S = 0
    total_S += If(C1 == 0, d1, 0)
    total_S += If(C2 == 0, d2 - d1 + 1, 0)
    total_S += If(C3 == 0, d3 - d2 + 1, 0)
    total_S += If(C4 == 0, 14 - d3, 0)  # 13 - d3 + 1 = 14 - d3
    s.add(total_S == 2)
    
    total_ST = 0
    total_ST += If(C1 == 1, d1, 0)
    total_ST += If(C2 == 1, d2 - d1 + 1, 0)
    total_ST += If(C3 == 1, d3 - d2 + 1, 0)
    total_ST += If(C4 == 1, 14 - d3, 0)
    s.add(total_ST == 7)
    
    total_P = 0
    total_P += If(C1 == 2, d1, 0)
    total_P += If(C2 == 2, d2 - d1 + 1, 0)
    total_P += If(C3 == 2, d3 - d2 + 1, 0)
    total_P += If(C4 == 2, 14 - d3, 0)
    s.add(total_P == 3)
    
    total_M = 0
    total_M += If(C1 == 3, d1, 0)
    total_M += If(C2 == 3, d2 - d1 + 1, 0)
    total_M += If(C3 == 3, d3 - d2 + 1, 0)
    total_M += If(C4 == 3, 14 - d3, 0)
    s.add(total_M == 4)
    
    # Day 7 must be in Stuttgart
    in_ST_7 = Or(
        And(C1 == 1, 1 <= 7, 7 <= d1),
        And(C2 == 1, d1 <= 7, 7 <= d2),
        And(C3 == 1, d2 <= 7, 7 <= d3),
        And(C4 == 1, d3 <= 7, 7 <= 13)
    )
    s.add(in_ST_7)
    
    # Day 13 must be in Stuttgart
    in_ST_13 = Or(
        And(C1 == 1, 1 <= 13, 13 <= d1),
        And(C2 == 1, d1 <= 13, 13 <= d2),
        And(C3 == 1, d2 <= 13, 13 <= d3),
        And(C4 == 1, d3 <= 13, 13 <= 13)
    )
    s.add(in_ST_13)
    
    # At least one day in [1,4] must be in Madrid
    in_Madrid = []
    for day in range(1, 5):  # days 1 to 4
        in_day = Or(
            And(C1 == 3, 1 <= day, day <= d1),
            And(C2 == 3, d1 <= day, day <= d2),
            And(C3 == 3, d2 <= day, day <= d3),
            And(C4 == 3, d3 <= day, day <= 13)
        )
        in_Madrid.append(in_day)
    s.add(Or(in_Madrid))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        d3_val = m[d3].as_long()
        C1_val = m[C1].as_long()
        C2_val = m[C2].as_long()
        C3_val = m[C3].as_long()
        C4_val = m[C4].as_long()
        
        city_map = {
            0: 'Seville',
            1: 'Stuttgart',
            2: 'Porto',
            3: 'Madrid'
        }
        
        # Build the itinerary
        itinerary_list = []
        for day in range(1, 14):  # days 1 to 13
            cities_this_day = []
            # Check segment1: [1, d1_val]
            if 1 <= day <= d1_val:
                cities_this_day.append(city_map[C1_val])
            # Check segment2: [d1_val, d2_val]
            if d1_val <= day <= d2_val:
                cities_this_day.append(city_map[C2_val])
            # Check segment3: [d2_val, d3_val]
            if d2_val <= day <= d3_val:
                cities_this_day.append(city_map[C3_val])
            # Check segment4: [d3_val, 13]
            if d3_val <= day <= 13:
                cities_this_day.append(city_map[C4_val])
            
            for city in cities_this_day:
                itinerary_list.append({"day": day, "place": city})
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()