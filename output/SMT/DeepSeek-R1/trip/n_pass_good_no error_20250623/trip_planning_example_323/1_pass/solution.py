from z3 import *

def main():
    # Define the cities and the flight graph
    cities = ['London', 'Split', 'Oslo', 'Porto']
    graph = {
        'London': ['Oslo', 'Split'],
        'Split': ['London', 'Oslo'],
        'Oslo': ['London', 'Split', 'Porto'],
        'Porto': ['Oslo']
    }
    durations = {
        'London': 7,
        'Split': 5,
        'Oslo': 2,
        'Porto': 5
    }
    
    # Create solver
    s = Solver()
    
    # Create variables for start and end days for each city
    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}
    
    # Create variables for the index (order) of each city
    idx = {city: Int(f'idx_{city}') for city in cities}
    
    # Fixed constraints for Split
    s.add(start['Split'] == 7)
    s.add(end['Split'] == 11)
    
    # Duration constraints for other cities
    for city in cities:
        if city != 'Split':
            s.add(end[city] == start[city] + durations[city] - 1)
    
    # London must start by day 7
    s.add(start['London'] <= 7)
    
    # All indices are distinct and between 0 and 3
    s.add(Distinct([idx[city] for city in cities]))
    for city in cities:
        s.add(idx[city] >= 0, idx[city] <= 3)
    
    # The first city (index 0) starts on day 1
    for city in cities:
        s.add(If(idx[city] == 0, start[city] == 1, True))
    
    # The last city (index 3) ends on day 16
    for city in cities:
        s.add(If(idx[city] == 3, end[city] == 16, True))
    
    # Consecutive cities: end of previous equals start of next
    for i in range(3):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    condition = And(idx[city1] == i, idx[city2] == i+1)
                    s.add(If(condition, end[city1] == start[city2], True))
    
    # Consecutive cities must have a direct flight
    for i in range(3):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    condition = And(idx[city1] == i, idx[city2] == i+1)
                    # Check if city2 is in the neighbors of city1
                    if city2 in graph[city1]:
                        s.add(If(condition, True, True))  # Always true if connected
                    else:
                        s.add(If(condition, False, True))  # Force false if not connected
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Determine the order of cities
        order = sorted(cities, key=lambda city: model.eval(idx[city]).as_long())
        itinerary_list = []
        
        # Build the itinerary
        for i, city in enumerate(order):
            s_val = model.eval(start[city]).as_long()
            e_val = model.eval(end[city]).as_long()
            
            # Add arrival record if not the first city
            if i > 0:
                itinerary_list.append({"day_range": f"Day {s_val}", "place": city})
            
            # Add continuous stay record
            itinerary_list.append({"day_range": f"Day {s_val}-{e_val}", "place": city})
            
            # Add departure record if not the last city
            if i < 3:
                itinerary_list.append({"day_range": f"Day {e_val}", "place": city})
        
        # Output the itinerary as JSON
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()