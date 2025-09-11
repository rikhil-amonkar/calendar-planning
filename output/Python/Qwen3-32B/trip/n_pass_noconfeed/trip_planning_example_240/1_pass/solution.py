import json

# Define the required days for each city
prague_days = 2
berlin_days = 3
stockholm_days = 5
tallinn_days = 5
total_days = 12

# Conference days in Berlin
conference_days_berlin = {6, 8}

# Direct flights (bidirectional)
direct_flights = {
    frozenset({'Berlin', 'Tallinn'}),
    frozenset({'Prague', 'Tallinn'}),
    frozenset({'Stockholm', 'Tallinn'}),
    frozenset({'Prague', 'Stockholm'}),
    frozenset({'Stockholm', 'Berlin'}),
}

def has_direct_flight(city_a, city_b):
    return frozenset({city_a, city_b}) in direct_flights

# Generate segments
segments = []

# Prague segment
prague_start = 1
prague_end = prague_start + prague_days - 1
segments.append({'city': 'Prague', 'start': prague_start, 'end': prague_end})

# Stockholm segment starts right after Prague ends (same day, since flight is on that day)
stockholm_start = prague_end
stockholm_end = stockholm_start + stockholm_days - 1
segments.append({'city': 'Stockholm', 'start': stockholm_start, 'end': stockholm_end})

# Berlin segment starts after Stockholm ends
berlin_start = stockholm_end
berlin_end = berlin_start + berlin_days - 1
segments.append({'city': 'Berlin', 'start': berlin_start, 'end': berlin_end})

# Tallinn segment starts after Berlin ends
tallinn_start = berlin_end
tallinn_end = tallinn_start + tallinn_days - 1
segments.append({'city': 'Tallinn', 'start': tallinn_start, 'end': tallinn_end})

# Check if all constraints are met
valid = True

# Check Berlin's conference days
berlin_segment = [s for s in segments if s['city'] == 'Berlin'][0]
berlin_days_covered = set(range(berlin_segment['start'], berlin_segment['end'] + 1))
if not conference_days_berlin.issubset(berlin_days_covered):
    valid = False

# Check Tallinn's stay includes days between 8-12
tallinn_segment = [s for s in segments if s['city'] == 'Tallinn'][0]
tallinn_days_covered = set(range(tallinn_segment['start'], tallinn_segment['end'] + 1))
required_tallinn_overlap = set(range(8, 13))  # days 8-12 inclusive
if not required_tallinn_overlap.issubset(tallinn_days_covered):
    valid = False

# Check direct flights between consecutive cities
cities_order = [s['city'] for s in segments]
for i in range(len(cities_order) - 1):
    current_city = cities_order[i]
    next_city = cities_order[i+1]
    if not has_direct_flight(current_city, next_city):
        valid = False

# Check total days
last_segment = segments[-1]
if last_segment['end'] != total_days:
    valid = False

if not valid:
    raise ValueError("The generated itinerary does not meet all constraints.")

# Convert segments to the required JSON format
itinerary = []
for segment in segments:
    day_range = f"Day {segment['start']}-{segment['end']}"
    place = segment['city']
    itinerary.append({"day_range": day_range, "place": place})

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))