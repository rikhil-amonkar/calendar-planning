import json

# Define the constraints
constraints = {
    "Riga": {"days": 2},
    "Frankfurt": {"days": 3},
    "Amsterdam": {"days": 2, "meet_friend": (2, 3)},
    "Vilnius": {"days": 5, "workshop": (7, 11)},
    "London": {"days": 2},
    "Stockholm": {"days": 3, "wedding": (13, 15)},
    "Bucharest": {"days": 4}
}

# Direct flights
direct_flights = {
    "London": ["Amsterdam", "Bucharest", "Frankfurt", "Stockholm"],
    "Amsterdam": ["London", "Stockholm", "Frankfurt", "Riga", "Vilnius", "Bucharest"],
    "Vilnius": ["Amsterdam", "Frankfurt", "Riga"],
    "Riga": ["Vilnius", "Frankfurt", "Stockholm", "Amsterdam", "Bucharest"],
    "Frankfurt": ["Vilnius", "Riga", "Stockholm", "Amsterdam", "London", "Bucharest"],
    "Bucharest": ["Riga", "Amsterdam", "Frankfurt", "London"],
    "Stockholm": ["London", "Amsterdam", "Frankfurt", "Riga"]
}

# Function to check if a transition is possible
def can_transition(city1, city2):
    return city2 in direct_flights[city1]

# Construct the itinerary
itinerary = []
current_day = 1
remaining_cities = set(constraints.keys())

# Place the fixed events first
# Vilnius workshop: Day 7-11
itinerary.append({"day_range": f"Day {7}-{11}", "place": "Vilnius"})
current_day = 12
remaining_cities.remove("Vilnius")

# Amsterdam meeting: Day 2-3
itinerary.append({"day_range": f"Day {2}-{3}", "place": "Amsterdam"})
current_day = 4
remaining_cities.remove("Amsterdam")

# Stockholm wedding: Day 13-15
itinerary.append({"day_range": f"Day {13}-{15}", "place": "Stockholm"})
current_day = 16
remaining_cities.remove("Stockholm")

# Fill in the remaining days
for city in remaining_cities:
    days = constraints[city]["days"]
    # Find a suitable starting day for the city
    start_day = current_day
    end_day = start_day + days - 1
    # Check if we can transition to this city
    if not itinerary:
        # No previous city, start from day 1
        start_day = 1
        end_day = start_day + days - 1
    else:
        # Check if we can transition from the last city in the itinerary
        last_city = itinerary[-1]["place"]
        if not can_transition(last_city, city):
            # Find a valid transition point
            for i in range(len(itinerary)):
                prev_city = itinerary[i]["place"]
                next_city = itinerary[i+1]["place"] if i+1 < len(itinerary) else None
                if can_transition(prev_city, city) and (next_city is None or can_transition(city, next_city)):
                    start_day = int(itinerary[i]["day_range"].split('-')[0].split(' ')[1])
                    end_day = start_day + days - 1
                    break
    
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    current_day = end_day + 1

# Sort the itinerary by day_range
itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[1]))

# Output the itinerary as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))