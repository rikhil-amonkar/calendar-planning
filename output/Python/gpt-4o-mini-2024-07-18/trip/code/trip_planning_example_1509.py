import json
from datetime import datetime, timedelta

# Define the trip constraints
city_constraints = {
    'Paris': {'days': 5, 'meeting_days': (4, 8)},
    'Warsaw': {'days': 2},
    'Krakow': {'days': 2, 'workshop_days': (17, 18)},
    'Tallinn': {'days': 2},
    'Riga': {'days': 2, 'wedding_days': (23, 24)},
    'Copenhagen': {'days': 5},
    'Helsinki': {'days': 5, 'meeting_days': (18, 22)},
    'Oslo': {'days': 5},
    'Santorini': {'days': 2, 'family_visit_days': (12, 13)},
    'Lyon': {'days': 4},
}

# Define direct flight connections
direct_flights = {
    'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Krakow', 'Oslo'],
    'Riga': ['Warsaw', 'Tallinn', 'Helsinki', 'Copenhagen'],
    'Tallinn': ['Warsaw', 'Riga', 'Helsinki', 'Oslo', 'Copenhagen'],
    'Copenhagen': ['Helsinki', 'Warsaw', 'Riga', 'Krakow', 'Oslo', 'Santorini'],
    'Krakow': ['Warsaw', 'Helsinki'],
    'Paris': ['Lyon', 'Oslo', 'Riga', 'Krakow', 'Tallinn', 'Copenhagen', 'Helsinki', 'Warsaw'],
    'Helsinki': ['Copenhagen', 'Warsaw', 'Riga', 'Krakow', 'Tallinn'],
    'Oslo': ['Copenhagen', 'Lyon', 'Riga', 'Warsaw', 'Krakow', 'Tallinn'],
    'Santorini': ['Copenhagen', 'Oslo'],
    'Lyon': ['Paris', 'Oslo']
}

# Function to plan the trip
def plan_trip(start_day=1, total_days=25):
    itinerary = []
    current_day = start_day
    
    # Visit Paris first
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Paris"]["days"] - 1}', 'place': 'Paris'})
    current_day += city_constraints["Paris"]["days"]

    # Meeting friends in Paris between day 4 and day 8
    meeting_start = 4
    meeting_end = 8

    # Schedule Warsaw
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Warsaw'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Warsaw"]["days"] - 1}', 'place': 'Warsaw'})
    current_day += city_constraints["Warsaw"]["days"]

    # Schedule Krakow
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Warsaw', 'to': 'Krakow'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Krakow"]["days"] - 1}', 'place': 'Krakow'})
    current_day += city_constraints["Krakow"]["days"]

    # Workshop in Krakow
    current_day += 1  # Move to day for workshop
    current_day += 1  # Move to day after workshop

    # Schedule Tallinn
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Tallinn'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Tallinn"]["days"] - 1}', 'place': 'Tallinn'})
    current_day += city_constraints["Tallinn"]["days"]

    # Schedule Riga
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Tallinn', 'to': 'Riga'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Riga"]["days"] - 1}', 'place': 'Riga'})
    current_day += city_constraints["Riga"]["days"]

    # Schedule Copenhagen
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Copenhagen'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Copenhagen"]["days"] - 1}', 'place': 'Copenhagen'})
    current_day += city_constraints["Copenhagen"]["days"]

    # Schedule Helsinki
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Copenhagen', 'to': 'Helsinki'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Helsinki"]["days"] - 1}', 'place': 'Helsinki'})
    current_day += city_constraints["Helsinki"]["days"]

    # Meeting in Helsinki
    current_day += 1  # Move for meeting
    current_day += 1  # Move for meeting

    # Schedule Oslo
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Helsinki', 'to': 'Oslo'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Oslo"]["days"] - 1}', 'place': 'Oslo'})
    current_day += city_constraints["Oslo"]["days"]

    # Schedule Santorini
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Santorini'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Santorini"]["days"] - 1}', 'place': 'Santorini'})
    current_day += city_constraints["Santorini"]["days"]

    # Schedule Lyon
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Santorini', 'to': 'Lyon'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + city_constraints["Lyon"]["days"] - 1}', 'place': 'Lyon'})
    current_day += city_constraints["Lyon"]["days"]

    return itinerary

# Generate the itinerary
trip_itinerary = plan_trip()

# Output in JSON format
json_output = json.dumps(trip_itinerary, indent=4)
print(json_output)