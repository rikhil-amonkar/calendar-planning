from z3 import *

def main():
    # City names and their indices
    city_names = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
    # Days required for each city (by index)
    days_req = [5, 4, 2, 4, 4, 2, 3]
    
    # Symmetric flight connections (undirected graph)
    edges_sym = set()
    edges_sym.add((0,3)); edges_sym.add((3,0))
    edges_sym.add((0,5)); edges_sym.add((5,0))
    edges_sym.add((0,6)); edges_sym.add((6,0))
    edges_sym.add((1,3)); edges_sym.add((3,1))
    edges_sym.add((2,3)); edges_sym.add((3,2))
    edges_sym.add((2,5)); edges_sym.add((5,2))
    edges_sym.add((2,6)); edges_sym.add((6,2))
    edges_sym.add((3,4)); edges_sym.add((4,3))
    edges_sym.add((3,5)); edges_sym.add((5,3))
    edges_sym.add((3,6)); edges_sym.add((6,3))
    edges_sym.add((4,5)); edges_sym.add((5,4))
    edges_sym.add((5,6)); edges_sym.add((6,5))
    
    # Create Z3 variables for the city in each of the 7 segments
    seg_city = [Int(f'seg_{i}') for i in range(7)]
    
    s = Solver()
    
    # Fix the first segment to Venice (index 0)
    s.add(seg_city[0] == 0)
    
    # The remaining segments must be distinct and in the range [1,6]
    for i in range(1, 7):
        s.add(seg_city[i] >= 1, seg_city[i] <= 6)
    
    # All segments must have distinct cities
    s.add(Distinct(seg_city))
    
    # Constraints for consecutive segments: must be connected by a direct flight
    for i in range(6):
        constraints = []
        for (a, b) in edges_sym:
            constraints.append(And(seg_city[i] == a, seg_city[i+1] == b))
        s.add(Or(constraints))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the sequence of cities
        city_sequence = [m.evaluate(seg_city[i]).as_long() for i in range(7)]
        
        # Compute start and end days for each segment
        start_days = [1]  # Start at day 1
        end_days = [1 + days_req[city_sequence[0]] - 1]  # End day for first segment
        
        for i in range(1, 7):
            start_days.append(end_days[i-1])  # Start next segment on the end day of the previous
            end_days.append(start_days[i] + days_req[city_sequence[i]] - 1)  # End day for current segment
        
        # Build the itinerary list
        itinerary = []
        for i in range(7):
            # Add the entire stay for the segment
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city_names[city_sequence[i]]})
            
            # If not the last segment, add flight records for the transition day
            if i < 6:
                day_x = end_days[i]  # Flight day
                # Departure from current city
                itinerary.append({"day_range": f"Day {day_x}", "place": city_names[city_sequence[i]]})
                # Arrival at next city
                itinerary.append({"day_range": f"Day {day_x}", "place": city_names[city_sequence[i+1]]})
        
        # Output the itinerary as a JSON-formatted dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()