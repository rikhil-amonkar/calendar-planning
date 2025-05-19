import json

# Define trip constraints
cities = ['Brussels', 'Barcelona', 'Split']
required_days = {'Brussels': 2, 'Barcelona': 7, 'Split': 5}
flight_connections = [('Brussels', 'Barcelona'), ('Barcelona', 'Split')]

# Calculate itinerary
current_day = 1
itinerary = []

# Brussels (must start on day 1)
brussels_end = current_day + required_days['Brussels'] - 1
itinerary.append({'day_range': f'Day {current_day}-{brussels_end}', 'place': 'Brussels'})

# Barcelona (flight on brussels_end day)
current_day = brussels_end
barcelona_end = current_day + required_days['Barcelona'] - 1
itinerary.append({'day_range': f'Day {current_day}-{barcelona_end}', 'place': 'Barcelona'})

# Split (flight on barcelona_end day)
current_day = barcelona_end
split_end = current_day + required_days['Split'] - 1
itinerary.append({'day_range': f'Day {current_day}-{split_end}', 'place': 'Split'})

# Validate total days
assert split_end == 12, "Invalid itinerary calculation"

# Output result
print(json.dumps({'itinerary': itinerary}))