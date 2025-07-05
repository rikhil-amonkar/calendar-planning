import z3
from collections import defaultdict

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    # Fixed events: city -> day ranges
    fixed_events = {
        'Madrid': [(6, 7)],
        'Vienna': [(3, 6)],
        'Riga': [(20, 23)],
        'Tallinn': [(23, 27)],
        'Krakow': [(11, 15)]
    }
    
    # Direct flights: adjacency list
    direct_flights = {
        'Vienna': ['Bucharest', 'Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga', 'Santorini'],
        'Bucharest': ['Vienna', 'Riga', 'Valencia', 'Santorini', 'Frankfurt', 'Madrid'],
        'Santorini': ['Madrid', 'Bucharest', 'Vienna'],
        'Madrid': ['Santorini', 'Valencia', 'Seville', 'Bucharest', 'Frankfurt'],
        'Seville': ['Valencia', 'Vienna', 'Madrid'],
        'Valencia': ['Seville', 'Madrid', 'Bucharest', 'Krakow', 'Frankfurt', 'Vienna'],
        'Riga': ['Bucharest', 'Tallinn', 'Frankfurt', 'Vienna'],
        'Tallinn': ['Riga', 'Frankfurt'],
        'Krakow': ['Valencia', 'Frankfurt', 'Vienna'],
        'Frankfurt': ['Valencia', 'Krakow', 'Vienna', 'Tallinn', 'Bucharest', 'Riga', 'Madrid']
    }
    
    # Create a reverse mapping for direct flights (undirected)
    for city in list(direct_flights.keys()):
        for other in direct_flights[city]:
            if city not in direct_flights[other]:
                direct_flights[other].append(city)
    
    # Initialize Z3 solver
    solver = z3.Solver()
    
    # Create variables: for each day, the city (or cities if it's a flight day)
    # We'll model each day as either a stay day (single city) or a flight day (two cities)
    # So for each day, we have a primary city, and optionally a secondary city (if flight)
    
    # Variables:
    # For each day, the current city (primary)
    primary = [z3.Int(f'primary_{day}') for day in range(1, 28)]
    # For each day, whether it's a flight day (0: no flight, 1: flight)
    is_flight = [z3.Int(f'is_flight_{day}') for day in range(1, 28)]
    # For flight days, the secondary city (arrival city)
    secondary = [z3.Int(f'secondary_{day}') for day in range(1, 28)]
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    num_cities = len(cities)
    
    # Constraints:
    # 1. Each primary and secondary (if flight) must be valid city IDs
    for day in range(1, 28):
        solver.add(z3.And(primary[day-1] >= 1, primary[day-1] <= num_cities))
        solver.add(z3.Or(is_flight[day-1] == 0, is_flight[day-1] == 1))
        solver.add(z3.Implies(is_flight[day-1] == 1, 
                             z3.And(secondary[day-1] >= 1, secondary[day-1] <= num_cities,
                                   primary[day-1] != secondary[day-1])))
    
    # 2. Flight days must have a direct flight between primary and secondary
    for day in range(1, 28):
        primary_city = primary[day-1]
        secondary_city = secondary[day-1]
        # For each possible primary city, the secondary city must be in its direct flights
        constraints = []
        for city, cid in city_ids.items():
            for other_city in direct_flights[city]:
                oid = city_ids[other_city]
                constraints.append(
                    z3.And(primary_city == cid, is_flight[day-1] == 1, secondary_city == oid)
                )
        solver.add(z3.Implies(is_flight[day-1] == 1, z3.Or(constraints)))
    
    # 3. Non-flight days: primary remains the same as the next day's primary unless it's a flight day
    for day in range(1, 27):
        # If day is not a flight day, primary[day] == primary[day+1]
        solver.add(z3.Implies(is_flight[day-1] == 0, primary[day-1] == primary[day]))
        # If day is a flight day, primary[day+1] == secondary[day]
        solver.add(z3.Implies(is_flight[day-1] == 1, primary[day] == secondary[day-1]))
    
    # 4. Fixed events:
    for city, day_ranges in fixed_events.items():
        cid = city_ids[city]
        for (start, end) in day_ranges:
            for day in range(start, end + 1):
                # The primary city must be this city on these days
                solver.add(primary[day-1] == cid)
                # Ensure no flight on these days (except possibly the first day)
                if day != start:
                    solver.add(is_flight[day-1] == 0)
    
    # 5. Total days per city must match the required days
    # Count for each city:
    city_days = {cid: 0 for cid in city_ids.values()}
    for day in range(1, 28):
        cid = primary[day-1]
        for city, id_ in city_ids.items():
            city_days[id_] += z3.If(cid == id_, 1, 0)
        # If it's a flight day, add 1 to the secondary city
        for city, id_ in city_ids.items():
            city_days[id_] += z3.If(z3.And(is_flight[day-1] == 1, secondary[day-1] == id_), 1, 0)
    
    for city, req_days in cities.items():
        cid = city_ids[city]
        solver.add(city_days[cid] == req_days)
    
    # 6. Additional constraints:
    # Santorini must be visited for 3 days (no fixed days)
    # Madrid's fixed days are 6-7, so other day must be another day (but Madrid's total is 2 days)
    # So Madrid is only on days 6 and 7.
    solver.add(z3.Or(primary[5] == city_ids['Madrid'], primary[6] == city_ids['Madrid']))
    solver.add(z3.Or(is_flight[5] == 0, is_flight[6] == 0))
    
    # Check if the solver can find a solution
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        
        # Helper function to get city name from ID
        def get_city(id_):
            return id_to_city[model.evaluate(id_).as_long()]
        
        current_day = 1
        while current_day <= 27:
            primary_city = get_city(primary[current_day - 1])
            flight_day = model.evaluate(is_flight[current_day - 1]).as_long() == 1
            if not flight_day:
                # Find consecutive days with the same primary city
                start_day = current_day
                end_day = current_day
                while end_day <= 27:
                    if (model.evaluate(is_flight[end_day - 1]).as_long() == 1 or 
                        get_city(primary[end_day - 1]) != primary_city):
                        break
                    end_day += 1
                end_day -= 1
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": primary_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": primary_city})
                current_day = end_day + 1
            else:
                secondary_city = get_city(secondary[current_day - 1])
                # Add the primary city for the day (departure)
                itinerary.append({"day_range": f"Day {current_day}", "place": primary_city})
                # Add the secondary city for the day (arrival)
                itinerary.append({"day_range": f"Day {current_day}", "place": secondary_city})
                current_day += 1
        
        # Now, adjust the itinerary to include day ranges for stays after flights
        # Reconstruct the itinerary to merge consecutive stays
        refined_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            entry = itinerary[i]
            day_range = entry['day_range']
            place = entry['place']
            if '-' in day_range:
                refined_itinerary.append(entry)
                i += 1
            else:
                day = int(day_range.split()[1])
                # Check if the next entry is the same place and day (flight case)
                if i + 1 < n and itinerary[i+1]['day_range'] == f"Day {day}":
                    # Flight day: add both entries
                    refined_itinerary.append({"day_range": f"Day {day}", "place": place})
                    refined_itinerary.append({"day_range": f"Day {day}", "place": itinerary[i+1]['place']})
                    i += 2
                    # Now, check if the next entries are consecutive stays
                    if i < n:
                        next_day = day + 1
                        next_entry = itinerary[i]
                        if next_entry['day_range'].startswith(f"Day {next_day}"):
                            # Find the end of the stay
                            start_day = next_day
                            j = i
                            while j < n:
                                current_entry = itinerary[j]
                                if not current_entry['day_range'].startswith(f"Day {start_day + (j - i)}"):
                                    break
                                if current_entry['place'] != itinerary[i]['place']:
                                    break
                                j += 1
                            end_day = start_day + (j - i) - 1
                            refined_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": itinerary[i]['place']})
                            i = j
                else:
                    refined_itinerary.append(entry)
                    i += 1
        
        # Final check to merge any consecutive same-place entries
        merged_itinerary = []
        i = 0
        while i < len(refined_itinerary):
            current = refined_itinerary[i]
            if i + 1 < len(refined_itinerary):
                next_entry = refined_itinerary[i+1]
                if (current['place'] == next_entry['place'] and 
                    current['day_range'].startswith('Day') and next_entry['day_range'].startswith('Day')):
                    # Merge them
                    start_day = int(current['day_range'].split()[1].split('-')[0])
                    end_day = int(next_entry['day_range'].split()[1].split('-')[-1])
                    merged_entry = {"day_range": f"Day {start_day}-{end_day}", "place": current['place']}
                    merged_itinerary.append(merged_entry)
                    i += 2
                else:
                    merged_itinerary.append(current)
                    i += 1
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_itinerary()
print(result)