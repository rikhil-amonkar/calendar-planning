import json

# Define the cities and their respective stay durations
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

# Define the special day constraints
special_days = {
    "Oslo": [(24, 25)],
    "Tallinn": [(4, 8)]
}

# Define the flight connections
flights = [
    ("Porto", "Oslo"), ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"),
    ("Riga", "Tallinn"), ("Edinburgh", "Porto"), ("Vilnius", "Helsinki"),
    ("Tallinn", "Vilnius"), ("Riga", "Oslo"), ("Geneva", "Oslo"),
    ("Edinburgh", "Oslo"), ("Edinburgh", "Helsinki"), ("Vilnius", "Oslo"),
    ("Riga", "Helsinki"), ("Budapest", "Geneva"), ("Helsinki", "Budapest"),
    ("Helsinki", "Oslo"), ("Edinburgh", "Riga"), ("Tallinn", "Helsinki"),
    ("Geneva", "Porto"), ("Budapest", "Oslo"), ("Helsinki", "Geneva"),
    ("Riga", "Vilnius"), ("Tallinn", "Oslo")
]

# Convert flights to a dictionary for quick lookup
flight_dict = {}
for city1, city2 in flights:
    if city1 not in flight_dict:
        flight_dict[city1] = []
    if city2 not in flight_dict:
        flight_dict[city2] = []
    flight_dict[city1].append(city2)
    flight_dict[city2].append(city1)

# Function to check if a city can be placed at a given start day
def can_place_city(itinerary, city, start_day):
    end_day = start_day + cities[city]
    if end_day > 25:
        return False
    for entry in itinerary:
        entry_start = int(entry["day_range"].split()[1].split('-')[0])
        entry_end = int(entry["day_range"].split()[1].split('-')[1]) if '-' in entry["day_range"] else entry_start
        if not (end_day <= entry_start or start_day >= entry_end + 1):
            return False
    if city in special_days:
        for start, end in special_days[city]:
            if not (end_day <= start or start_day >= end + 1):
                return False
    return True

# Function to add a city to the itinerary
def add_city(itinerary, city, start_day):
    end_day = start_day + cities[city]
    itinerary.append({"day_range": f"Day {start_day}-{end_day-1}", "place": city})
    for i in range(start_day, end_day):
        if i != start_day:
            itinerary.append({"day_range": f"Day {i}", "place": city})
    return itinerary

# Backtracking function to construct the itinerary
def backtrack(itinerary, remaining_cities):
    if not remaining_cities:
        return itinerary if int(itinerary[-1]["day_range"].split()[1].split('-')[1]) == 25 else None
    for city in remaining_cities:
        for start_day in range(1, 26 - cities[city] + 1):
            if can_place_city(itinerary, city, start_day):
                new_itinerary = add_city(itinerary.copy(), city, start_day)
                result = backtrack(new_itinerary, [c for c in remaining_cities if c != city])
                if result:
                    return result
    return None

# Start with an empty itinerary and the list of all cities
remaining_cities = list(cities.keys())
itinerary = backtrack([], remaining_cities)

# Print the final itinerary
if itinerary:
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")