from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Istanbul': 2,
        'Rome': 3,
        'Seville': 4,
        'Naples': 7,
        'Santorini': 4
    }
    city_list = list(cities.keys())
    
    # Direct flights (undirected)
    direct_flights = [
        ('Rome', 'Santorini'),
        ('Rome', 'Seville'),
        ('Rome', 'Naples'),
        ('Rome', 'Istanbul'),
        ('Naples', 'Istanbul'),
        ('Naples', 'Santorini')
    ]
    flight_pairs = {}
    for a, b in direct_flights:
        flight_pairs.setdefault(a, set()).add(b)
        flight_pairs.setdefault(b, set()).add(a)
    
    s = Solver()
    
    # For each day, the city the traveler is in
    # For flight days, two cities are assigned (departure and arrival)
    day_city = [[Bool(f'day_{day}_city_{city}') for city in city_list] for day in range(16)]
    
    # Each day must be in at least one city
    for day in range(16):
        s.add(Or(day_city[day]))
    
    # No two cities on the same day unless it's a flight day
    # For non-flight days, exactly one city is assigned
    # For flight days, two cities are assigned, and they must be connected by a direct flight
    for day in range(16):
        # Count the number of cities per day
        city_count = Sum([If(day_city[day][i], 1, 0) for i in range(len(city_list))])
        s.add(Or(city_count == 1, city_count == 2))
        if city_count == 2:
            # The two cities must be connected by a direct flight
            for i in range(len(city_list)):
                for j in range(i+1, len(city_list)):
                    city_i = city_list[i]
                    city_j = city_list[j]
                    if city_j not in flight_pairs.get(city_i, set()):
                        s.add(Not(And(day_city[day][i], day_city[day][j])))
    
    # Transition constraints: if day d is a flight day (two cities), then day d+1's city must be one of the two
    for day in range(15):
        current_day_cities = day_city[day]
        next_day_cities = day_city[day+1]
        # If current day is a flight day (two cities), then next day's city must be one of them
        flight_day = Sum([If(current_day_cities[i], 1, 0) for i in range(len(city_list))]) == 2
        if flight_day:
            # The next day's city must be one of the two cities of the current day
            s.add(Or([And(current_day_cities[i], next_day_cities[i]) for i in range(len(city_list))]))
    
    # Fixed constraints
    # Istanbul between day 6 and 7 (1-based: days 5 and 6 in 0-based)
    s.add(day_city[5][city_list.index('Istanbul')])
    s.add(day_city[6][city_list.index('Istanbul')])
    
    # Santorini between day 13-16 (1-based: days 12-15 in 0-based)
    for day in range(12, 16):
        s.add(day_city[day][city_list.index('Santorini')])
    
    # Total days per city
    for city in cities:
        total = Sum([If(day_city[day][city_list.index(city)], 1, 0) for day in range(16)])
        s.add(total == cities[city])
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        current_place = None
        start_day = 0  # 0-based
        for day in range(16):
            # Determine the cities for this day
            day_cities = [city for city in city_list if model.evaluate(day_city[day][city_list.index(city)])]
            if len(day_cities) == 1:
                place = day_cities[0]
                if place != current_place:
                    if current_place is not None:
                        # End previous stay
                        end_day = day - 1
                        if start_day == end_day:
                            itinerary.append({"day_range": f"Day {start_day+1}", "place": current_place})
                        else:
                            itinerary.append({"day_range": f"Day {start_day+1}-{end_day+1}", "place": current_place})
                    current_place = place
                    start_day = day
            else:
                # Flight day: two cities
                if current_place is not None:
                    # End previous stay
                    end_day = day - 1
                    if start_day <= end_day:
                        if start_day == end_day:
                            itinerary.append({"day_range": f"Day {start_day+1}", "place": current_place})
                        else:
                            itinerary.append({"day_range": f"Day {start_day+1}-{end_day+1}", "place": current_place})
                # Add flight day entries
                itinerary.append({"day_range": f"Day {day+1}", "place": day_cities[0]})
                itinerary.append({"day_range": f"Day {day+1}", "place": day_cities[1]})
                current_place = day_cities[1]
                start_day = day + 1
        
        # Add the last stay
        if current_place is not None and start_day < 16:
            end_day = 15
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day+1}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day+1}-{end_day+1}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))