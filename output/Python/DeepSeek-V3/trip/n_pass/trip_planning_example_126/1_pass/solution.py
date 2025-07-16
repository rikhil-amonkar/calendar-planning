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
    # Must be in Krakow between day 1-5, and total 5 days in Krakow
    # So Krakow must be the first city
    itinerary = []
    
    # Assign Krakow days (must include days 1-5)
    # Since we have to be in Krakow for 5 days, and the workshop is days 1-5,
    # the simplest is to stay in Krakow for days 1-5
    itinerary.append({"day_range": "Day 1-5", "place": "Krakow"})
    remaining_krakow_days = days_in_krakow - 5
    current_day = 6
    
    # Next, we have to go to Paris (only connection from Krakow)
    # Transition day: day 6 is in both Krakow and Paris
    if remaining_krakow_days > 0:
        itinerary.append({"day_range": f"Day {current_day}", "place": "Krakow and Paris"})
        remaining_krakow_days -= 1
    else:
        itinerary.append({"day_range": f"Day {current_day}", "place": "Krakow and Paris"})
    current_day += 1
    
    # Assign Paris days (total 2 days, one is the transition day)
    remaining_paris_days = days_in_paris - 1
    if remaining_paris_days > 0:
        itinerary.append({"day_range": f"Day {current_day}", "place": "Paris"})
        current_day += 1
    
    # Next, go to Seville (only connection from Paris)
    # Transition day: current_day is in both Paris and Seville
    itinerary.append({"day_range": f"Day {current_day}", "place": "Paris and Seville"})
    current_day += 1
    
    # Assign Seville days (total 6 days, one is the transition day)
    remaining_seville_days = days_in_seville - 1
    if remaining_seville_days > 0:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + remaining_seville_days - 1}", "place": "Seville"})
        current_day += remaining_seville_days
    
    # Verify total days
    total_planned_days = 0
    for entry in itinerary:
        day_range = entry['day_range']
        if '-' in day_range:
            start, end = map(int, day_range.replace('Day ', '').split('-'))
            total_planned_days += (end - start + 1)
        else:
            total_planned_days += 1
    
    # If total days is less than 11, extend Seville stay
    if total_planned_days < total_days:
        extra_days = total_days - total_planned_days
        last_entry = itinerary[-1]
        if last_entry['place'] == 'Seville':
            current_end = int(last_entry['day_range'].split('-')[-1])
            new_end = current_end + extra_days
            last_entry['day_range'] = f"Day {current_end - (remaining_seville_days - 1)}-{new_end}"
    
    return {"itinerary": itinerary}

# Compute and output the itinerary
result = compute_itinerary()
print(json.dumps(result, indent=2))