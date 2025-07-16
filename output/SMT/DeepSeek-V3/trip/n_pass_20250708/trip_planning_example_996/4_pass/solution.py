from z3 import *
import json

def solve_itinerary():
    cities = ['Mykonos', 'Nice', 'Prague', 'Zurich', 'Bucharest', 'Valencia', 'Riga']
    city_days = {
        'Mykonos': 3,
        'Nice': 2,
        'Prague': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Valencia': 5,
        'Riga': 5
    }
    
    direct_flights = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Prague': ['Bucharest', 'Riga', 'Valencia', 'Zurich'],
        'Zurich': ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Valencia', 'Riga'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Valencia': ['Bucharest', 'Prague', 'Zurich'],
        'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague']
    }
    
    num_days = 22
    s = Solver()
    
    # Variables: for each day, list of possible cities (at least one, possibly two)
    day_city = [[Bool(f"day_{day}_{city}") for city in cities] for day in range(num_days)]
    
    # Each day must have at least one city and at most two cities
    for day in range(num_days):
        # At least one city per day
        s.add(Or([day_city[day][i] for i in range(len(cities))]))
        # At most two cities per day
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                for k in range(j + 1, len(cities)):
                    s.add(Not(And(day_city[day][i], day_city[day][j], day_city[day][k])))
    
    # Mykonos must be visited on days 1-3 (0-based days 0-2)
    for day in range(3):
        s.add(day_city[day][cities.index('Mykonos')])
    
    # Prague must be visited on days 7-9 (0-based days 6-8)
    for day in range(6, 9):
        s.add(day_city[day][cities.index('Prague')])
    
    # Total days per city
    for city in cities:
        total = 0
        for day in range(num_days):
            total += If(day_city[day][cities.index(city)], 1, 0)
        s.add(total == city_days[city])
    
    # Flight constraints: if two cities on the same day, they must have a direct flight
    for day in range(num_days):
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                city1 = cities[i]
                city2 = cities[j]
                both_cities = And(day_city[day][i], day_city[day][j])
                s.add(Implies(both_cities, Or([city2 in direct_flights[city1]])))
    
    # Consecutive days: if different cities, must have a direct flight
    for day in range(num_days - 1):
        current_day = day
        next_day = day + 1
        for i in range(len(cities)):
            for j in range(len(cities)):
                if i != j:
                    # If current day ends in city i and next day starts in city j, there must be a flight
                    transition = And(day_city[current_day][i], day_city[next_day][j])
                    s.add(Implies(transition, Or([cities[j] in direct_flights[cities[i]]])))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Build day sequence
        day_places = []
        for day in range(num_days):
            places = []
            for i in range(len(cities)):
                if m.evaluate(day_city[day][i]):
                    places.append(cities[i])
            day_places.append(places)
        
        # Generate itinerary
        current_place = None
        start_day = 1
        for day in range(num_days):
            day_num = day + 1
            places = day_places[day]
            if len(places) == 1:
                place = places[0]
                if current_place != place:
                    if current_place is not None:
                        # End previous stay
                        itinerary.append({
                            "day_range": f"Day {start_day}-{day}",
                            "place": current_place
                        })
                    # Start new stay
                    current_place = place
                    start_day = day_num
                    itinerary.append({
                        "day_range": f"Day {day_num}",
                        "place": place
                    })
                else:
                    pass  # continuation
            else:
                # Flight day: two cities
                if current_place is not None:
                    # End previous stay
                    itinerary.append({
                        "day_range": f"Day {start_day}-{day}",
                        "place": current_place
                    })
                # Add flight day entries
                for place in places:
                    itinerary.append({
                        "day_range": f"Day {day_num}",
                        "place": place
                    })
                # The next stay starts with the arrival city
                current_place = places[-1]
                start_day = day_num + 1 if day_num < num_days else day_num
        
        # Add the last stay
        if current_place is not None and start_day <= num_days:
            itinerary.append({
                "day_range": f"Day {start_day}-{num_days}",
                "place": current_place
            })
        
        # Post-process to merge consecutive same-city entries
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i + 1 < n and itinerary[i+1]['place'] == current['place']:
                # Merge consecutive entries for the same place
                start_day = int(current['day_range'].split('-')[0].split(' ')[1])
                end_day = int(itinerary[i+1]['day_range'].split('-')[-1])
                merged = {
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current['place']
                }
                merged_itinerary.append(merged)
                i += 2
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))