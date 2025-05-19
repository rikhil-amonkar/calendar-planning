import json

# Define input parameters
days_per_city = {'Stuttgart': 6, 'Seville': 7, 'Manchester': 4}
flight_map = {'Manchester': ['Seville', 'Stuttgart'], 'Seville': ['Manchester'], 'Stuttgart': ['Manchester']}

# Determine valid route considering constraints and flights
route = ['Stuttgart', 'Manchester', 'Seville']

# Calculate day ranges with flight day overlaps
itinerary = []
current_day = 1

for i, city in enumerate(route):
    duration = days_per_city[city]
    end_day = current_day + duration - 1
    itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
    current_day = end_day  # Next city starts on same day via direct flight

# Verify total days match
assert current_day - 1 == 15, "Invalid itinerary calculation"

# Output result
print(json.dumps({'itinerary': itinerary}))