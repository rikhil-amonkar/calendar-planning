import json
import z3

def main():
    # Define the direct flight connections as a set of tuples (bidirectional)
    direct_flights = set([
        ('Edinburgh', 'Berlin'), ('Amsterdam', 'Berlin'), ('Edinburgh', 'Amsterdam'),
        ('Vienna', 'Berlin'), ('Berlin', 'Brussels'), ('Vienna', 'Reykjavik'),
        ('Edinburgh', 'Brussels'), ('Vienna', 'Brussels'), ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Brussels'), ('Amsterdam', 'Vienna'), ('Reykjavik', 'Berlin')
    ])
    
    # Duration of stay for each city
    duration = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }
    
    # Fixed start days for some cities
    start_days = {
        'Amsterdam': 5,
        'Reykjavik': 12,
        'Berlin': 16,
        'Edinburgh': 1,
        'Vienna': 8,
        'Brussels': 19
    }
    
    # Order of cities in the itinerary
    order = ['Edinburgh', 'Amsterdam', 'Vienna', 'Reykjavik', 'Berlin', 'Brussels']
    
    # Initialize Z3 solver
    solver = z3.Solver()
    
    # Create Z3 variables for start days
    start_z3 = {city: z3.Int(f'start_{city}') for city in start_days}
    
    # Fix start days to the solution values
    for city, day in start_days.items():
        solver.add(start_z3[city] == day)
    
    # Add constraints for consecutive cities: end of current city equals start of next
    for i in range(5):
        city_i = order[i]
        city_j = order[i+1]
        end_i = start_z3[city_i] + duration[city_i] - 1
        solver.add(end_i == start_z3[city_j])
    
    # Add fixed constraints for Amsterdam, Reykjavik, and Berlin
    solver.add(start_z3['Amsterdam'] == 5)
    solver.add(start_z3['Amsterdam'] + duration['Amsterdam'] - 1 == 8)
    solver.add(start_z3['Berlin'] == 16)
    solver.add(start_z3['Berlin'] + duration['Berlin'] - 1 == 19)
    solver.add(start_z3['Reykjavik'] == 12)
    solver.add(start_z3['Reykjavik'] + duration['Reykjavik'] - 1 == 16)
    
    # First city starts at day 1, last city ends at day 23
    solver.add(start_z3[order[0]] == 1)
    last_city = order[-1]
    solver.add(start_z3[last_city] + duration[last_city] - 1 == 23)
    
    # Verify flight connections
    flight_ok = True
    for i in range(5):
        a, b = order[i], order[i+1]
        if (a, b) not in direct_flights and (b, a) not in direct_flights:
            flight_ok = False
            break
    if not flight_ok:
        solver.add(False)  # Make the constraints unsatisfiable if flight connection is missing
    
    # Check if the constraints are satisfied
    if solver.check() == z3.sat:
        # Build itinerary
        itinerary = []
        # First city: Edinburgh
        first_city = order[0]
        s0 = start_days[first_city]
        e0 = s0 + duration[first_city] - 1
        itinerary.append({"day_range": f"Day {s0}-{e0}", "place": first_city})
        itinerary.append({"day_range": f"Day {e0}", "place": first_city})
        
        # Middle cities: Amsterdam, Vienna, Reykjavik, Berlin
        for i in range(1, 5):
            city = order[i]
            s = start_days[city]
            e = s + duration[city] - 1
            itinerary.append({"day_range": f"Day {s}", "place": city})
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
            itinerary.append({"day_range": f"Day {e}", "place": city})
        
        # Last city: Brussels
        last_city = order[5]
        s_last = start_days[last_city]
        e_last = s_last + duration[last_city] - 1
        itinerary.append({"day_range": f"Day {s_last}", "place": last_city})
        itinerary.append({"day_range": f"Day {s_last}-{e_last}", "place": last_city})
        
        # Output the result as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == "__main__":
    main()