import json

def plan_trip():
    # Constants
    total_days = 18
    itinerary = []

    # Trip Constraints
    trip_details = {
        "Mykonos": {"days": 4, "meet_relatives": (15, 18)},
        "Krakow": {"days": 5},
        "Vilnius": {"days": 2},
        "Helsinki": {"days": 2},
        "Dubrovnik": {"days": 3, "show_days": (2, 4)},
        "Oslo": {"days": 2, "meet_friends": (1, 2)},
        "Madrid": {"days": 5},
        "Paris": {"days": 2}
    }

    # Direct flights mapping
    direct_flights = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Vilnius', 'Dubrovnik'],
        'Krakow': ['Oslo', 'Vilnius', 'Paris'],
        'Vilnius': ['Helsinki', 'Krakow', 'Paris'],
        'Helsinki': ['Oslo', 'Vilnius', 'Krakow', 'Madrid', 'Paris', 'Dubrovnik'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Madrid': ['Paris', 'Mykonos', 'Dubrovnik', 'Oslo'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Vilnius'],
        'Mykonos': []
    }

    # Itinerary calculation
    current_day = 1
    current_location = 'Oslo'
    
    # Meeting Friends in Oslo
    itinerary.append({'day_range': 'Day 1-2', 'place': current_location})
    
    # Traveling to Dubrovnik for the show
    current_day += 2
    current_location = 'Dubrovnik'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Dubrovnik'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': current_location})
    
    # (Day 5 onward)
    current_day += 3

    # Traveling to Krakow
    current_location = 'Krakow'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Krakow'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': current_location})
    
    current_day += 5
    
    # Traveling to Vilnius
    current_location = 'Vilnius'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Vilnius'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_location})

    current_day += 2

    # Traveling to Helsinki
    current_location = 'Helsinki'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Vilnius', 'to': 'Helsinki'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_location})

    current_day += 2

    # Traveling to Paris
    current_location = 'Paris'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Helsinki', 'to': 'Paris'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': current_location})

    current_day += 2

    # Traveling to Madrid
    current_location = 'Madrid'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Madrid'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': current_location})

    current_day += 5

    # Traveling to Mykonos
    current_location = 'Mykonos'
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Madrid', 'to': 'Mykonos'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': current_location})

    current_day += 4

    # Final JSON output
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    print(plan_trip())