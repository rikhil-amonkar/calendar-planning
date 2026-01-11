import json
from collections import defaultdict

# Define the graph of direct flights
graph = defaultdict(set)
connections = [
    ("Zurich", "Brussels"), ("Bucharest", "Copenhagen"), ("Venice", "Brussels"),
    ("Nice", "Zurich"), ("Hamburg", "Nice"), ("Zurich", "Naples"),
    ("Hamburg", "Bucharest"), ("Zurich", "Copenhagen"), ("Bucharest", "Brussels"),
    ("Hamburg", "Brussels"), ("Venice", "Naples"), ("Venice", "Copenhagen"),
    ("Bucharest", "Naples"), ("Hamburg", "Copenhagen"), ("Venice", "Zurich"),
    ("Nice", "Brussels"), ("Hamburg", "Venice"), ("Copenhagen", "Naples"),
    ("Nice", "Naples"), ("Hamburg", "Zurich"), ("Salzburg", "Hamburg"),
    ("Zurich", "Bucharest"), ("Brussels", "Naples"), ("Copenhagen", "Brussels"),
    ("Venice", "Nice"), ("Nice", "Copenhagen")
]

for city1, city2 in connections:
    graph[city1].add(city2)
    graph[city2].add(city1)

# Define the constraints
constraints = {
    "Salzburg": (2, None),
    "Venice": (5, None),
    "Bucharest": (4, None),
    "Brussels": (2, (21, 22)),
    "Hamburg": (4, None),
    "Copenhagen": (4, (18, 21)),
    "Nice": (3, (9, 11)),
    "Zurich": (5, None),
    "Naples": (4, (22, 25))
}

# Initialize the itinerary
itinerary = []
current_day = 1

# Helper function to add to itinerary
def add_to_itinerary(city, days, specific_days=None):
    global current_day
    if specific_days:
        start_day, end_day = specific_days
        if end_day - start_day + 1 != days:
            raise ValueError(f"Specific days for {city} do not match required days.")
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    else:
        end_day = current_day + days - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1

# Add fixed events first
add_to_itinerary("Nice", 3, (9, 11))  # Visit relatives in Nice
add_to_itinerary("Copenhagen", 4, (18, 21))  # Attend wedding in Copenhagen
add_to_itinerary("Brussels", 2, (21, 22))  # Meet friends in Brussels
add_to_itinerary("Naples", 4, (22, 25))  # Attend workshop in Naples

# Remaining cities to allocate
remaining_cities = ["Salzburg", "Venice", "Bucharest", "Hamburg", "Zurich"]

# Function to check if we can move from one city to another
def can_move(from_city, to_city):
    return to_city in graph[from_city] or from_city in graph[to_city]

# Allocate remaining days
for city, (days, _) in constraints.items():
    if city in remaining_cities:
        # Find a place to insert this city
        inserted = False
        for i, entry in enumerate(itinerary):
            start_day, _ = map(int, entry["day_range"].split("-"))
            if i == 0 and start_day > days:
                add_to_itinerary(city, days)
                inserted = True
                break
            elif i > 0:
                prev_end_day = int(itinerary[i-1]["day_range"].split("-")[1])
                if start_day - prev_end_day - 1 >= days and can_move(itinerary[i-1]["place"], city):
                    add_to_itinerary(city, days, (prev_end_day + 1, prev_end_day + days))
                    inserted = True
                    break
            if not inserted and i == len(itinerary) - 1:
                end_day = int(entry["day_range"].split("-")[1])
                if 25 - end_day >= days and can_move(entry["place"], city):
                    add_to_itinerary(city, days, (end_day + 1, end_day + days))
                    inserted = True
                    break
        if not inserted:
            raise ValueError(f"Could not find a suitable place to insert {city}")

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))