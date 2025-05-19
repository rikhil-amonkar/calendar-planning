import json
from datetime import datetime, timedelta

def calculate_trip_plan():
    # Define trip constraints
    total_days = 26
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    events = {
        'Barcelona': (10, 12),
        'Copenhagen': (7, 10),
        'Dubrovnik': (16, 20)
    }
    direct_flights = [
        ('Copenhagen', 'Athens'), ('Copenhagen', 'Dubrovnik'), ('Munich', 'Tallinn'), 
        ('Copenhagen', 'Munich'), ('Venice', 'Munich'), ('Reykjavik', 'Athens'), 
        ('Athens', 'Dubrovnik'), ('Venice', 'Athens'), ('Lyon', 'Barcelona'), 
        ('Copenhagen', 'Reykjavik'), ('Reykjavik', 'Munich'), ('Athens', 'Munich'), 
        ('Lyon', 'Munich'), ('Barcelona', 'Reykjavik'), ('Venice', 'Copenhagen'), 
        ('Barcelona', 'Dubrovnik'), ('Lyon', 'Venice'), ('Dubrovnik', 'Munich'), 
        ('Barcelona', 'Athens'), ('Copenhagen', 'Barcelona'), ('Venice', 'Barcelona'), 
        ('Barcelona', 'Munich'), ('Barcelona', 'Tallinn'), ('Copenhagen', 'Tallinn')
    ]

    # Initialize trip plan
    trip_plan = []
    current_day = 1
    current_city = None

    # Prioritize cities with events
    prioritized_cities = sorted(cities.keys(), key=lambda x: events.get(x, (float('inf'), float('inf')))[0] if x in events else float('inf'))

    # Visit cities with events first
    for city in prioritized_cities:
        if city in events:
            event_start, event_end = events[city]
            if current_day < event_start:
                # Fill gap with other cities
                for other_city in cities:
                    if other_city not in prioritized_cities and other_city!= city:
                        days_to_spend = min(event_start - current_day, cities[other_city])
                        trip_plan.append({'day_range': f'Day {current_day}-{current_day + days_to_spend - 1}', 'place': other_city})
                        current_day += days_to_spend
                        cities[other_city] -= days_to_spend
                        if cities[other_city] == 0:
                            del cities[other_city]
            # Visit city with event
            trip_plan.append({'day_range': f'Day {event_start}-{event_end}', 'place': city})
            current_day = event_end + 1
            cities[city] = 0
            del cities[city]

    # Visit remaining cities
    while cities:
        # Find city with direct flight from current city
        next_city = None
        for city in cities:
            if current_city and (current_city, city) in direct_flights:
                next_city = city
                break
            elif current_city and (city, current_city) in direct_flights:
                next_city = city
                break
        if not next_city:
            # If no direct flight, choose any city
            next_city = list(cities.keys())[0]
        # Visit next city
        days_to_spend = cities[next_city]
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + days_to_spend - 1}', 'place': next_city})
        current_day += days_to_spend
        del cities[next_city]
        # Add flight to trip plan
        if current_city:
            trip_plan.append({'flying': f'Day {current_day-1}-{current_day-1}', 'from': current_city, 'to': next_city})
        current_city = next_city

    # Add last flight to trip plan if necessary
    if current_day <= total_days:
        trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': current_city, 'to': 'Home'})

    return trip_plan

if __name__ == '__main__':
    trip_plan = calculate_trip_plan()
    print(json.dumps(trip_plan, indent=4))