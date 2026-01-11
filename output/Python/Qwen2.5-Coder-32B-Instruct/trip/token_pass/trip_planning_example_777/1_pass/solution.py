import json

# Define the constraints
days_in_city = {
    'Dublin': 5,
    'Helsinki': 3,
    'Riga': 3,
    'Reykjavik': 2,
    'Vienna': 2,
    'Tallinn': 5
}

# Define the special events
special_events = {
    'Helsinki': (3, 5),  # Meet friends
    'Vienna': (2, 3),   # Annual show
    'Tallinn': (7, 11)  # Wedding
}

# Define the available direct flights
flights = [
    ('Helsinki', 'Riga'), ('Riga', 'Tallinn'), ('Vienna', 'Helsinki'),
    ('Riga', 'Dublin'), ('Vienna', 'Riga'), ('Reykjavik', 'Vienna'),
    ('Helsinki', 'Dublin'), ('Tallinn', 'Dublin'), ('Reykjavik', 'Helsinki'),
    ('Reykjavik', 'Dublin'), ('Helsinki', 'Tallinn'), ('Vienna', 'Dublin')
]

# Convert flights to a set for quick lookup
flight_set = set(flights + [(b, a) for a, b in flights])

def is_valid_itinerary(itinerary):
    # Check if the total duration is 15 days
    if sum(days_in_city[city] for city in days_in_city) != 15:
        return False
    
    # Check if all special events are covered
    current_day = 1
    for city, days in itinerary:
        if city in special_events:
            event_start, event_end = special_events[city]
            if not (event_start <= current_day <= event_end):
                return False
        current_day += days
    
    # Check if all flights are direct
    current_city = itinerary[0][0]
    for next_city, _ in itinerary[1:]:
        if (current_city, next_city) not in flight_set:
            return False
        current_city = next_city
    
    return True

def generate_itinerary():
    # Start with Dublin as it has the longest stay
    start_city = 'Dublin'
    cities_to_visit = list(days_in_city.keys())
    cities_to_visit.remove(start_city)
    
    # Try different permutations of remaining cities
    import itertools
    for order in itertools.permutations(cities_to_visit):
        itinerary = [(start_city, days_in_city[start_city])]
        current_day = days_in_city[start_city]
        
        for city in order:
            itinerary.append((city, days_in_city[city]))
            current_day += days_in_city[city]
        
        if is_valid_itinerary(itinerary):
            return itinerary
    
    return None

def format_itinerary(itinerary):
    formatted_itinerary = []
    current_day = 1
    for city, days in itinerary:
        end_day = current_day + days - 1
        formatted_itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1
    return formatted_itinerary

# Generate and format the itinerary
itinerary = generate_itinerary()
if itinerary:
    result = {"itinerary": format_itinerary(itinerary)}
    print(json.dumps(result, indent=4))
else:
    print("No valid itinerary found.")