import json

def plan_trip():
    # Define the itinerary parameters
    total_days = 12
    cities = {
        "Frankfurt": {"days": 3},
        "Naples": {"days": 4},
        "Helsinki": {"days": 4, "show_days": (2, 5)},
        "Lyon": {"days": 3},
        "Prague": {"days": 2, "workshop_day": 1}
    }
    
    # Itinerary generation
    itinerary = []
    current_day = 1
    
    # Day 1: Workshop in Prague
    itinerary.append({'day_range': f'Day {current_day}-{current_day}', 'place': 'Prague'})
    current_day += 1
    
    # Day 2-5: Attend show in Helsinki
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Prague', 'to': 'Helsinki'})
    itinerary.append({'day_range': f'Day {current_day + 1}-{current_day + 4}', 'place': 'Helsinki'})
    current_day += 4
    
    # Day 5: Travel to Naples
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Helsinki', 'to': 'Naples'})
    current_day += 1
    
    # Day 6-9: Stay in Naples
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 3}', 'place': 'Naples'})
    current_day += 4
    
    # Day 9: Travel to Frankfurt
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Naples', 'to': 'Frankfurt'})
    current_day += 1
    
    # Day 10-12: Stay in Frankfurt
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 2}', 'place': 'Frankfurt'})
    
    # Day 12: Travel to Lyon
    # Continuing after Frankfurt (but we included all days already in Frankfurt)
    itinerary.append({'flying': f'Day {current_day + 2}-{current_day + 2}', 'from': 'Frankfurt', 'to': 'Lyon'})
    
    # Day 12: Stay in Lyon
    itinerary.append({'day_range': f'Day {current_day + 2}-{current_day + 2}', 'place': 'Lyon'})

    # Convert the itinerary to JSON format
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)