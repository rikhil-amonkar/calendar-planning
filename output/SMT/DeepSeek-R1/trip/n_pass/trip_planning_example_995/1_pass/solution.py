from z3 import *

def main():
    # Define the cities for segments 3 to 7
    cities = ["Stuttgart", "Venice", "Split", "Brussels", "Copenhagen"]
    req_dict = {
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Brussels": 3,
        "Copenhagen": 3
    }
    
    # Create Z3 variables for the 5 segments (segments 3 to 7)
    segments = [Const(f'seg_{i}', StringSort()) for i in range(5)]
    
    s = Solver()
    
    # Each segment must be one of the cities and all distinct
    s.add(Distinct(segments))
    for seg in segments:
        s.add(Or([seg == city for city in cities]))
    
    # List of direct flights (as undirected edges)
    flights = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels")
    ]
    
    # Function to check flight connection
    def are_connected(c1, c2):
        options = []
        for (a, b) in flights:
            options.append(And(c1 == a, c2 == b))
            options.append(And(c1 == b, c2 == a))
        return Or(options)
    
    # Constraint: segment3 (first in the list) must be connected to Oslo
    s.add(are_connected("Oslo", segments[0]))
    
    # Constraints for consecutive segments
    for i in range(4):
        s.add(are_connected(segments[i], segments[i+1]))
    
    # Brussels constraints: not in segment3, and if in segment4 then segment3 must be Venice or Split
    s.add(Not(segments[0] == "Brussels"))
    s.add(Or(
        And(segments[1] == "Brussels", Or(segments[0] == "Venice", segments[0] == "Split")),
        segments[2] == "Brussels",
        segments[3] == "Brussels"
    ))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        seg_assign = [m[seg].as_string() for seg in segments]
        print("Found a valid assignment:")
        print(seg_assign)
        
        # Full segment cities: segment1: Barcelona, segment2: Oslo, then segments3-7: seg_assign
        all_cities = ["Barcelona", "Oslo"] + seg_assign
        # Required days for each segment
        all_req = [3, 2] + [req_dict[city] for city in seg_assign]
        
        # Compute start and end days for each segment
        starts = [0] * 7
        ends = [0] * 7
        starts[0] = 1
        ends[0] = starts[0] + all_req[0] - 1
        for i in range(1, 7):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + all_req[i] - 1
        
        # Build itinerary list
        itinerary = []
        # First, the contiguous stays
        for i in range(7):
            s_val = starts[i]
            e_val = ends[i]
            if s_val == e_val:
                day_str = f"Day {s_val}"
            else:
                day_str = f"Day {s_val}-{e_val}"
            itinerary.append({"day_range": day_str, "place": all_cities[i]})
        
        # Then, the flight days (for segments 1 to 6)
        for i in range(6):
            flight_day = ends[i]  # same as starts[i+1]
            itinerary.append({"day_range": f"Day {flight_day}", "place": all_cities[i]})
            itinerary.append({"day_range": f"Day {flight_day}", "place": all_cities[i+1]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print("Itinerary:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()