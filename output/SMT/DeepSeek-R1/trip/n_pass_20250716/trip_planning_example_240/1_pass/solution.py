from z3 import *
import json

def main():
    # Define the city mapping
    city_map = {
        0: 'Prague',
        1: 'Berlin',
        2: 'Tallinn',
        3: 'Stockholm'
    }
    
    # Flight pairs: bidirectional direct flights
    flight_pairs = [(0,2), (2,0), (1,2), (2,1), (3,2), (2,3), (0,3), (3,0), (3,1), (1,3)]
    
    # Create solver
    s = Solver()
    
    # City variables for each segment
    c1, c2, c3, c4 = Ints('c1 c2 c3 c4')
    
    # Constraints: each city variable must be between 0 and 3
    s.add(c1 >= 0, c1 <= 3)
    s.add(c2 >= 0, c2 <= 3)
    s.add(c3 >= 0, c3 <= 3)
    s.add(c4 >= 0, c4 <= 3)
    
    # All cities in segments must be distinct
    s.add(Distinct(c1, c2, c3, c4))
    
    # Fixed segments: last segment is Tallinn (2), third segment is Berlin (1)
    s.add(c4 == 2)  # Tallinn
    s.add(c3 == 1)  # Berlin
    
    # Flight constraints: consecutive segments must have direct flights
    # Flight from segment1 to segment2
    s.add(Or([And(c1 == a, c2 == b) for (a, b) in flight_pairs]))
    # Flight from segment2 to segment3
    s.add(Or([And(c2 == a, c3 == b) for (a, b) in flight_pairs]))
    # Flight from segment3 to segment4
    s.add(Or([And(c3 == a, c4 == b) for (a, b) in flight_pairs]))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        
        # Segment boundaries (fixed based on constraints)
        segments = [
            (1, 2, city_map[c1_val]),  # Segment 1: start day, end day, city
            (2, 6, city_map[c2_val]),  # Segment 2
            (6, 8, city_map[c3_val]),  # Segment 3
            (8, 12, city_map[c4_val])  # Segment 4
        ]
        
        # Build itinerary
        itinerary = []
        for idx, (start, end, city) in enumerate(segments):
            # Add contiguous block for the segment
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            
            # If not the last segment, add flight day records
            if idx < len(segments) - 1:
                next_city = segments[idx+1][2]
                itinerary.append({"day_range": f"Day {end}", "place": city})
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        # Output the itinerary as a JSON dictionary
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()