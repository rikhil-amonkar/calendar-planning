from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Variables for the cities of the three stays after Warsaw
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    
    # Variables for the end days of the second and third stays
    a = Int('a')  # end day of stay1 (which starts at day2)
    b = Int('b')  # end day of stay2 (which starts at day a)
    
    # Constraints for s1, s2, s3: each is one of 1,2,3 (Budapest, Paris, Riga) and they are distinct
    s.add(s1 >= 1, s1 <= 3)
    s.add(s2 >= 1, s2 <= 3)
    s.add(s3 >= 1, s3 <= 3)
    s.add(Distinct(s1, s2, s3))
    
    # Constraints for a and b: a is at least 2, b is at least a, and both at most 17
    s.add(a >= 2, a <= 17)
    s.add(b >= a, b <= 17)
    
    # Days in each city (city0: Warsaw, city1: Budapest, city2: Paris, city3: Riga)
    # Warsaw: stay0: days 1 to 2 -> 2 days (fixed)
    # For the other cities: sum over the stays
    days_city1 = If(s1 == 1, a - 1, 0) + If(s2 == 1, b - a + 1, 0) + If(s3 == 1, 17 - b + 1, 0)
    days_city2 = If(s1 == 2, a - 1, 0) + If(s2 == 2, b - a + 1, 0) + If(s3 == 2, 17 - b + 1, 0)
    days_city3 = If(s1 == 3, a - 1, 0) + If(s2 == 3, b - a + 1, 0) + If(s3 == 3, 17 - b + 1, 0)
    
    s.add(days_city1 == 7)  # Budapest
    s.add(days_city2 == 4)  # Paris
    s.add(days_city3 == 7)  # Riga
    
    # Wedding constraint: must be in Riga during day11 to day17
    s.add(Or(
        And(s1 == 3, a >= 11),   # Riga in stay1 (ends at a) and a>=11
        And(s2 == 3, b >= 11),    # Riga in stay2 (ends at b) and b>=11
        s3 == 3                  # Riga in stay3 (ends at 17) -> always in [11,17]
    ))
    
    # Function to check direct flight
    def direct_flight(c1, c2):
        return Or(
            And(c1 == 0, c2 == 1), And(c1 == 0, c2 == 2), And(c1 == 0, c2 == 3),
            And(c1 == 1, c2 == 0), And(c1 == 1, c2 == 2),
            And(c1 == 2, c2 == 0), And(c1 == 2, c2 == 1), And(c1 == 2, c2 == 3),
            And(c1 == 3, c2 == 0), And(c1 == 3, c2 == 2)
        )
    
    # Flight constraints: 
    s.add(direct_flight(0, s1))  # from Warsaw (0) to s1
    s.add(direct_flight(s1, s2)) # from s1 to s2
    s.add(direct_flight(s2, s3)) # from s2 to s3
    
    # Check if there is a solution
    if s.check() == sat:
        m = s.model()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        
        # Map city indices to names
        city_names = {
            0: "Warsaw",
            1: "Budapest",
            2: "Paris",
            3: "Riga"
        }
        s1_name = city_names[s1_val]
        s2_name = city_names[s2_val]
        s3_name = city_names[s3_val]
        
        # Function to format day range
        def format_day_range(start, end):
            if start == end:
                return "Day " + str(start)
            else:
                return "Day {}-{}".format(start, end)
        
        # Build itinerary
        itinerary = [
            {"day_range": "Day 1-2", "place": "Warsaw"},
            {"day_range": "Day 2", "place": "Warsaw"},
            {"day_range": "Day 2", "place": s1_name},
            {"day_range": format_day_range(2, a_val), "place": s1_name},
            {"day_range": "Day " + str(a_val), "place": s1_name},
            {"day_range": "Day " + str(a_val), "place": s2_name},
            {"day_range": format_day_range(a_val, b_val), "place": s2_name},
            {"day_range": "Day " + str(b_val), "place": s2_name},
            {"day_range": "Day " + str(b_val), "place": s3_name},
            {"day_range": format_day_range(b_val, 17), "place": s3_name}
        ]
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()