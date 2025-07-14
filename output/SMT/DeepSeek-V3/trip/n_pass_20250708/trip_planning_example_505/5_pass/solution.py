from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Prague": 4,
        "Stuttgart": 2,
        "Split": 2,
        "Krakow": 2,
        "Florence": 2
    }
    
    # Direct flight connections
    connections = {
        "Stuttgart": ["Split", "Krakow"],
        "Prague": ["Florence", "Split", "Krakow"],
        "Krakow": ["Stuttgart", "Split", "Prague"],
        "Split": ["Stuttgart", "Krakow", "Prague"],
        "Florence": ["Prague"]
    }
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each city's start and end day
    city_vars = {}
    for city in cities:
        start = Int(f'start_{city}')
        end = Int(f'end_{city}')
        city_vars[city] = (start, end)
        # Constraints: start >=1, end <=8, start <= end
        s.add(start >= 1)
        s.add(end <= 8)
        s.add(start <= end)
        # Duration constraint: end - start + 1 == required days
        s.add(end - start + 1 == cities[city])
    
    # Constraint for the wedding in Stuttgart between day 2 and 3
    stuttgart_start, stuttgart_end = city_vars["Stuttgart"]
    s.add(Or(
        And(stuttgart_start <= 2, stuttgart_end >= 2),
        And(stuttgart_start <= 3, stuttgart_end >= 3)
    ))
    
    # Constraint for meeting friends in Split between day 3 and 4
    split_start, split_end = city_vars["Split"]
    s.add(Or(
        And(split_start <= 3, split_end >= 3),
        And(split_start <= 4, split_end >= 4)
    ))
    
    # Calculate number of flights (overlapping days)
    # We know total city days sum to 12 (4+2+2+2+2)
    # And actual trip days are 8, so flights = (12 - 8) = 4
    num_flights = 4
    
    # Create flight variables - which cities are connected by flights
    flight_vars = {}
    for city1 in cities:
        for city2 in cities:
            if city1 != city2 and city2 in connections[city1]:
                flight = Bool(f'flight_{city1}_{city2}')
                flight_vars[(city1, city2)] = flight
                # Flight implies city1's end day equals city2's start day
                s.add(Implies(flight, 
                             And(city_vars[city1][1] == city_vars[city2][0],
                                 city_vars[city1][1] >= 1,
                                 city_vars[city1][1] <= 8)))
    
    # Exactly num_flights flights must occur
    s.add(PbEq([(f, 1) for f in flight_vars.values()], num_flights))
    
    # Ensure no overlapping stays except for flight days
    for city1 in cities:
        for city2 in cities:
            if city1 != city2:
                s1, e1 = city_vars[city1]
                s2, e2 = city_vars[city2]
                # Either no overlap, or overlap only on flight day
                flight_condition = Or(
                    And(e1 == s2, flight_vars.get((city1, city2), False)),
                    And(e2 == s1, flight_vars.get((city2, city1), False))
                )
                s.add(Or(
                    e1 < s2,  # city1 ends before city2 starts
                    e2 < s1,  # city2 ends before city1 starts
                    flight_condition
                ))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Get all city stays sorted by start day
        stays = []
        for city in cities:
            start = m.evaluate(city_vars[city][0]).as_long()
            end = m.evaluate(city_vars[city][1]).as_long()
            stays.append((start, end, city))
        stays.sort()
        
        # Build itinerary
        prev_end = 0
        prev_city = None
        for start, end, city in stays:
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            # Check for flight day
            if prev_end != 0 and prev_end == start:
                itinerary.append({"day_range": f"Day {prev_end}", "place": prev_city})
                itinerary.append({"day_range": f"Day {start}", "place": city})
            prev_end = end
            prev_city = city
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)