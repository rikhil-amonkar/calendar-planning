from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = ['Split', 'Vilnius', 'Madrid', 'Santorini']
    required_days = {
        'Split': 5,
        'Vilnius': 4,
        'Madrid': 6,
        'Santorini': 2
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Vilnius', 'Split'),
        ('Split', 'Madrid'),
        ('Madrid', 'Santorini')
    ]
    # Make it bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    total_days = 14
    days = list(range(1, total_days + 1))
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city is the traveler in?
    # day_city[d][c] is True if on day d, the traveler is in city c.
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in days]
    
    # Constraints:
    
    # 1. Each day, the traveler is in at least one city (can be two on flight days)
    for day in days:
        s.add(Or([day_city[day-1][i] for i in range(len(cities))]))
    
    # 2. Total days per city
    for city in cities:
        total = 0
        for day in days:
            idx = cities.index(city)
            total += If(day_city[day-1][idx], 1, 0)
        s.add(total == required_days[city])
    
    # 3. Conference days: days 13 and 14 in Santorini
    santorini_idx = cities.index('Santorini')
    s.add(day_city[12][santorini_idx])  # Day 13
    s.add(day_city[13][santorini_idx])  # Day 14
    
    # 4. Flight transitions: if on day d city A and day d+1 city B, then (A,B) must be a flight.
    for day in range(1, total_days):
        for c1 in cities:
            for c2 in cities:
                if c1 == c2:
                    continue
                c1_idx = cities.index(c1)
                c2_idx = cities.index(c2)
                # If day is in c1 and day+1 is in c2, then (c1, c2) must be a flight.
                s.add(Implies(
                    And(day_city[day-1][c1_idx], day_city[day][c2_idx]),
                    (c1, c2) in all_flights
                ))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        # Extract the day sequence
        day_sequence = []
        for day in days:
            current_cities = []
            for city in cities:
                if is_true(model.eval(day_city[day-1][cities.index(city)])):
                    current_cities.append(city)
            day_sequence.append(current_cities)
        
        # Build the itinerary
        itinerary = []
        current_stays = {}  # city: start_day
        
        for day in days:
            current_day_cities = day_sequence[day-1]
            # Cities that are newly added (flight arrivals)
            new_cities = [city for city in current_day_cities if city not in current_stays]
            # Cities that are departed (flight departures)
            departed_cities = [city for city in current_stays if city not in current_day_cities]
            
            # Process departed cities: add their stay up to day-1
            for city in departed_cities:
                start_day = current_stays[city]
                end_day = day - 1
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                del current_stays[city]
            
            # Process new cities: add the flight day entry for each
            for city in new_cities:
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_stays[city] = day
        
        # Add any remaining stays after the last day
        for city, start_day in current_stays.items():
            end_day = total_days
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        
        # Remove duplicates and sort the itinerary
        unique_itinerary = []
        seen = set()
        for item in itinerary:
            key = (item["day_range"], item["place"])
            if key not in seen:
                seen.add(key)
                unique_itinerary.append(item)
        
        # Sort the itinerary by day range
        unique_itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[1]))
        
        return {"itinerary": unique_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))