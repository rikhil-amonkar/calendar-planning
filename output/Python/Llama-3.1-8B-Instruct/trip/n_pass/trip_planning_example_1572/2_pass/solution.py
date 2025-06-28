import json
from collections import defaultdict

# Define the trip constraints
cities = {
    "Lyon": 3,
    "Paris": 5,
    "Riga": 2,
    "Berlin": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

direct_flights = {
    ("Paris", "Stockholm"): 1,
    ("Seville", "Paris"): 1,
    ("Naples", "Zurich"): 1,
    ("Nice", "Riga"): 1,
    ("Berlin", "Milan"): 1,
    ("Paris", "Zurich"): 1,
    ("Paris", "Nice"): 1,
    ("Milan", "Paris"): 1,
    ("Milan", "Riga"): 1,
    ("Paris", "Lyon"): 1,
    ("Milan", "Naples"): 1,
    ("Paris", "Riga"): 1,
    ("Berlin", "Stockholm"): 1,
    ("Stockholm", "Riga"): 1,
    ("Nice", "Zurich"): 1,
    ("Milan", "Zurich"): 1,
    ("Lyon", "Nice"): 1,
    ("Zurich", "Stockholm"): 1,
    ("Zurich", "Riga"): 1,
    ("Berlin", "Naples"): 1,
    ("Milan", "Stockholm"): 1,
    ("Berlin", "Zurich"): 1,
    ("Milan", "Seville"): 1,
    ("Paris", "Naples"): 1,
    ("Berlin", "Riga"): 1,
    ("Nice", "Stockholm"): 1,
    ("Berlin", "Paris"): 1,
    ("Nice", "Naples"): 1,
    ("Berlin", "Nice"): 1
}

# Define the special events
special_events = {
    ("Berlin", 1): 1,
    ("Berlin", 2): 1,
    ("Stockholm", 20): 1,
    ("Stockholm", 21): 1,
    ("Stockholm", 22): 1,
    ("Nice", 12): 1,
    ("Nice", 13): 1
}

# Initialize the itinerary
itinerary = defaultdict(int)
total_days = 23
current_day = 1

# Add the special events to the itinerary
for (city, day), duration in special_events.items():
    itinerary[(day, day + duration)] = city
    current_day = day + duration

# Add the city stays to the itinerary
for city, duration in cities.items():
    if city == "Berlin":
        # Add the wedding in Berlin
        itinerary[(1, 2)] = city
        current_day = 2
    elif city == "Stockholm":
        # Add the annual show in Stockholm
        itinerary[(20, 22)] = city
        current_day = 22
    elif city == "Nice":
        # Add the workshop in Nice
        itinerary[(12, 13)] = city
        current_day = 13
    else:
        itinerary[(current_day, current_day + duration)] = city
        current_day += duration

# Add the transitions between cities
for (city1, city2), duration in direct_flights.items():
    if city1 in itinerary and city2 in itinerary:
        start_day = itinerary[(city1, city2)]
        end_day = start_day + duration
        itinerary[(start_day, end_day)] = city2
        current_day = end_day

# Ensure the itinerary covers exactly 23 days
if current_day < total_days:
    # Find the last city in the itinerary
    last_city = list(itinerary.keys())[-1]
    last_day = last_city[1]
    
    # Calculate the number of days remaining
    remaining_days = total_days - last_day
    
    # Add the remaining days to the itinerary
    next_city = list(cities.keys())[0]
    itinerary[(last_day + 1, last_day + remaining_days + 1)] = next_city

# Convert the itinerary to a list of day-place mappings
day_place_mappings = []
for (start_day, end_day), city in itinerary.items():
    day_range = f"Day {start_day}-{end_day}"
    day_place_mappings.append({"day_range": day_range, "place": city})

# Output the result as a JSON-formatted dictionary
result = {"itinerary": day_place_mappings}
print(json.dumps(result, indent=4))