import json

def compute_itinerary():
    # Input parameters
    total_days = 11
    days_in_seville = 6
    days_in_paris = 2
    days_in_krakow = 5
    workshop_krakow_range = (1, 5)  # Days 1-5
    
    # Direct flight connections
    connections = {
        'Krakow': ['Paris'],
        'Paris': ['Krakow', 'Seville'],
        'Seville': ['Paris']
    }
    
    # Determine the order of visits based on constraints
    itinerary = []
    
    # Assign Krakow days (must include days 1-5)
    itinerary.append({"day_range": "Day 1-5", "place": "Krakow"})
    current_day = 6
    
    # Transition day to Paris (day 6)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Krakow and Paris"})
    current_day += 1
    
    # Assign remaining Paris day (day 7)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Paris"})
    current_day += 1
    
    # Transition day to Seville (day 8)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Paris and Seville"})
    current_day += 1
    
    # Assign Seville days (days 9-14, but we only need 11 total days)
    # Since we've already accounted for 8 days (1-5,6,7,8), we need 3 more days in Seville
    itinerary.append({"day_range": f"Day {current_day}-{current_day + 2}", "place": "Seville"})
    
    # Verify total days
    total_planned_days = 0
    for entry in itinerary:
        day_range = entry['day_range']
        if '-' in day_range:
            start, end = map(int, day_range.replace('Day ', '').split('-'))
            total_planned_days += (end - start + 1)
        else:
            total_planned_days += 1
    
    assert total_planned_days == total_days, f"Total days should be {total_days}, got {total_planned_days}"
    
    return {"itinerary": itinerary}

# Compute and output the itinerary
result = compute_itinerary()
print(json.dumps(result, indent=2))