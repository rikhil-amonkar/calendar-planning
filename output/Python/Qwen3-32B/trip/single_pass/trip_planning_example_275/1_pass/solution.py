import json

# Define the parameters
required_days = {
    'Vilnius': 4,
    'Split': 5,
    'Madrid': 6,
    'Santorini': 2
}

# Determine the correct order based on flight connections and constraints
order = ['Vilnius', 'Split', 'Madrid', 'Santorini']

itinerary = []
current_start = 1

for city in order:
    days_needed = required_days[city]
    end_day = current_start + days_needed - 1
    day_range = f"Day {current_start}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = end_day  # Next city starts on the same day as the flight day

# Output as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))