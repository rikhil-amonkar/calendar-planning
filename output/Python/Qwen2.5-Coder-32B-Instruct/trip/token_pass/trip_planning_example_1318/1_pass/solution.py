import json

# Define the cities and their required stay durations
cities = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

# Define the fixed constraints
fixed_constraints = {
    "Oslo": (24, 25),
    "Tallinn": (4, 8)
}

# Define the direct flight connections
direct_flights = {
    "Porto": ["Oslo", "Edinburgh", "Geneva"],
    "Edinburgh": ["Budapest", "Geneva", "Oslo", "Porto", "Riga", "Helsinki"],
    "Riga": ["Tallinn", "Oslo", "Edinburgh", "Helsinki", "Vilnius"],
    "Tallinn": ["Vilnius", "Oslo", "Riga", "Helsinki"],
    "Budapest": ["Geneva", "Oslo", "Helsinki"],
    "Vilnius": ["Oslo", "Riga", "Helsinki", "Tallinn"],
    "Helsinki": ["Oslo", "Budapest", "Geneva", "Riga", "Vilnius", "Tallinn", "Edinburgh"],
    "Geneva": ["Oslo", "Edinburgh", "Porto", "Budapest", "Helsinki"],
    "Oslo": ["Porto", "Edinburgh", "Geneva", "Budapest", "Helsinki", "Riga", "Tallinn", "Vilnius"]
}

# Initialize the itinerary
itinerary = []

# Function to add a city to the itinerary
def add_city(city, start_day):
    end_day = start_day + cities[city] - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    return end_day

# Add fixed constraints to the itinerary
current_day = 1
for city, (start, end) in fixed_constraints.items():
    if start == current_day:
        current_day = add_city(city, start) + 1

# Add other cities to the itinerary
remaining_cities = [city for city in cities if city not in fixed_constraints]
remaining_days = 25 - sum(cities[city] for city in fixed_constraints)

# Sort cities by duration in descending order to try fitting longer stays first
remaining_cities.sort(key=lambda x: cities[x], reverse=True)

# Try to fit each city into the remaining days
for city in remaining_cities:
    # Find a place to fit the city
    found_place = False
    for i in range(current_day, 26 - cities[city] + 1):
        # Check if the city can be placed starting from day i
        can_place = True
        for existing in itinerary:
            existing_start, existing_end = map(int, existing["day_range"].split("-")[0].split()[1]), map(int, existing["day_range"].split("-")[1])
            if not (i > existing_end or i + cities[city] - 1 < existing_start):
                can_place = False
                break
        if can_place:
            current_day = add_city(city, i) + 1
            found_place = True
            break
    if not found_place:
        raise ValueError(f"Could not find a suitable place for {city} in the itinerary")

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))