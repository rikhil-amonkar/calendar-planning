import json

# Define trip constraints
cities = ["Riga", "Amsterdam", "Mykonos"]
durations = {"Riga": 2, "Amsterdam": 2, "Mykonos": 5}
flight_connections = {("Riga", "Amsterdam"), ("Amsterdam", "Riga"), ("Amsterdam", "Mykonos"), ("Mykonos", "Amsterdam")}
# The relatives visit constraint requires Riga to be first
itinerary_order = ["Riga", "Amsterdam", "Mykonos"]

# Verify that the chosen itinerary order has valid direct flights between consecutive cities
valid_order = True
for i in range(len(itinerary_order) - 1):
    if (itinerary_order[i], itinerary_order[i + 1]) not in flight_connections:
        valid_order = False
        break

itinerary = []
current_day = 1

if valid_order:
    for city in itinerary_order:
        duration = durations[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))