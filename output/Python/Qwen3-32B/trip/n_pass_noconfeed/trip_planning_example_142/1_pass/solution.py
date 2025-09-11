import json

# Define trip constraints
madrid_days = 4
dublin_days = 3
tallinn_days = 2

# Define valid flight connections (bidirectional)
valid_connections = {('Madrid', 'Dublin'), ('Dublin', 'Tallinn')}

# Determine valid city sequence that satisfies all constraints
# The sequence must end with Tallinn for the workshop on days 6-7
# And must follow valid flight connections
city_sequence = ['Madrid', 'Dublin', 'Tallinn']

# Verify sequence is valid
valid = True
for i in range(len(city_sequence) - 1):
    if (city_sequence[i], city_sequence[i+1]) not in valid_connections:
        valid = False
        break

if not valid:
    raise ValueError("No valid city sequence found that satisfies all constraints")

# Calculate itinerary day ranges
itinerary = []
current_start = 1

for city in city_sequence:
    days = locals()[f"{city.lower()}_days"]
    end_day = current_start + days - 1
    itinerary.append({
        "day_range": f"Day {current_start}-{end_day}",
        "place": city
    })
    current_start = end_day

# Format output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))