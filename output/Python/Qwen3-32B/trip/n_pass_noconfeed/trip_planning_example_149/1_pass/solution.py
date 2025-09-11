import json

# Define input variables
total_days = 10
durations = {
    'London': 3,
    'Santorini': 6,
    'Istanbul': 3
}
conference_days = [5, 10]
flight_connections = {
    'Istanbul': ['London'],
    'London': ['Istanbul', 'Santorini'],
    'Santorini': ['London']
}

# Determine the order of cities based on constraints
order = ['Istanbul', 'London', 'Santorini']

# Compute the itinerary
itinerary = []
current_day = 1
for city in order:
    duration = durations[city]
    end_day = current_day + duration - 1
    day_range = f"Day {current_day}-{end_day}"
    itinerary.append({'day_range': day_range, 'place': city})
    current_day = end_day

# Validate conference days are within Santorini stay
santorini_start = None
santorini_end = None
for entry in itinerary:
    if entry['place'] == 'Santorini':
        parts = entry['day_range'].split()
        santorini_start = int(parts[1].split('-')[0])
        santorini_end = int(parts[2])
        break

for day in conference_days:
    if not (santorini_start <= day <= santorini_end):
        raise ValueError("Conference days not within Santorini stay")

# Output as JSON
output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))