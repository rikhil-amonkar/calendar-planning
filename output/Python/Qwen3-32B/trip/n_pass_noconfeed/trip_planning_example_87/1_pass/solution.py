import json

# Define the cities and required days
cities = ["Riga", "Amsterdam", "Mykonos"]
required_days = {
    "Riga": 2,
    "Amsterdam": 2,
    "Mykonos": 5
}

# Determine the order of cities based on direct flights and constraints
# Since Riga must be first, followed by Amsterdam, then Mykonos
order = ["Riga", "Amsterdam", "Mykonos"]

# Calculate the day ranges for each city
itinerary = []
current_day = 1

for city in order:
    days = required_days[city]
    end_day = current_day + days - 1
    itinerary.append({
        "day_range": f"Day {current_day}-{end_day}",
        "place": city
    })
    current_day = end_day + 1  # Move to the next day after the current city's stay

# Prepare the output dictionary
output = {"itinerary": itinerary}

# Print the JSON-formatted output
print(json.dumps(output, indent=2))