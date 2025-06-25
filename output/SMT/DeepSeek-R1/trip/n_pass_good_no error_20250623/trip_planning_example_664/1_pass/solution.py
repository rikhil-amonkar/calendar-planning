from z3 import *
import json

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the cities and their durations
    cities = ["Bucharest", "Munich", "Seville", "Milan", "Stockholm", "Tallinn"]
    durations = {
        "Bucharest": 4,
        "Munich": 5,
        "Seville": 5,
        "Milan": 2,
        "Stockholm": 5,
        "Tallinn": 2
    }
    
    # Create start day variables for each city
    starts = {city: Int(f'start_{city}') for city in cities}
    
    # Compute end days: end = start + duration - 1
    ends = {city: starts[city] + durations[city] - 1 for city in cities}
    
    # Fixed constraints for Bucharest, Munich, Seville
    s.add(starts["Bucharest"] == 1)
    s.add(starts["Munich"] == 4)
    s.add(starts["Seville"] == 8)
    
    # Flight connection constraints: end of current city == start of next city
    route = ["Bucharest", "Munich", "Seville", "Milan", "Stockholm", "Tallinn"]
    for i in range(len(route) - 1):
        s.add(ends[route[i]] == starts[route[i+1]])
    
    # All start days >= 1 and end days <= 18
    for city in cities:
        s.add(starts[city] >= 1)
        s.add(ends[city] <= 18)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_vals = {city: m.evaluate(starts[city]).as_long() for city in cities}
        end_vals = {city: start_vals[city] + durations[city] - 1 for city in cities}
        
        # Build the itinerary
        itinerary_list = []
        for i, city in enumerate(route):
            start = start_vals[city]
            end = end_vals[city]
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
            if i < len(route) - 1:
                itinerary_list.append({"day_range": f"Day {end}", "place": city})
                next_city = route[i+1]
                itinerary_list.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()