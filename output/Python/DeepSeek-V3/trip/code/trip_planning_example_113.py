import json

def plan_trip():
    # Input parameters
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 7
    seville_show_start = 9
    seville_show_end = 12
    
    # Direct flights available
    direct_flights = {
        'Milan': ['Seville'],
        'Naples': ['Milan'],
        'Seville': ['Milan']
    }
    
    # Validate total days
    if (naples_days + seville_days + milan_days) != total_days:
        return {"error": "Total days do not add up to 12"}
    
    # Determine the itinerary
    itinerary = []
    
    # Seville show is from day 9 to 12, so must be in Seville during that time
    # So Seville must be the last city
    # We need to fit Naples and Milan before day 9
    
    # Option 1: Start with Naples
    # Naples can only fly to Milan
    # Then Milan can fly to Seville
    
    # Calculate days for Naples and Milan before Seville
    days_before_seville = seville_show_start - 1
    
    # Assign Naples first
    naples_end = naples_days
    itinerary.append({'day_range': f'Day 1-{naples_end}', 'place': 'Naples'})
    
    # Fly to Milan
    fly_day = naples_end
    itinerary.append({'flying': f'Day {fly_day}-{fly_day}', 'from': 'Naples', 'to': 'Milan'})
    
    # Calculate remaining days for Milan before Seville
    milan_before_seville = days_before_seville - naples_end
    if milan_before_seville < 0:
        return {"error": "Cannot fit Milan before Seville show"}
    
    milan_end = fly_day + milan_before_seville
    itinerary.append({'day_range': f'Day {fly_day + 1}-{milan_end}', 'place': 'Milan'})
    
    # Fly to Seville
    fly_day = milan_end
    itinerary.append({'flying': f'Day {fly_day}-{fly_day}', 'from': 'Milan', 'to': 'Seville'})
    
    # Stay in Seville for the remaining days
    seville_start = fly_day + 1
    seville_end = total_days
    itinerary.append({'day_range': f'Day {seville_start}-{seville_end}', 'place': 'Seville'})
    
    # Verify all constraints are met
    # Check Naples days
    naples_actual = 0
    for entry in itinerary:
        if 'place' in entry and entry['place'] == 'Naples':
            start, end = map(int, entry['day_range'].split('-')[0].replace('Day ', '').split('-')[0]), \
                         map(int, entry['day_range'].split('-')[1].replace('Day ', '').split('-')[0])
            naples_actual += end - start + 1
    if naples_actual != naples_days:
        return {"error": "Naples days constraint not met"}
    
    # Check Seville days
    seville_actual = 0
    for entry in itinerary:
        if 'place' in entry and entry['place'] == 'Seville':
            start, end = map(int, entry['day_range'].split('-')[0].replace('Day ', '').split('-')[0]), \
                         map(int, entry['day_range'].split('-')[1].replace('Day ', '').split('-')[0])
            seville_actual += end - start + 1
    if seville_actual != seville_days:
        return {"error": "Seville days constraint not met"}
    
    # Check Milan days
    milan_actual = 0
    for entry in itinerary:
        if 'place' in entry and entry['place'] == 'Milan':
            start, end = map(int, entry['day_range'].split('-')[0].replace('Day ', '').split('-')[0]), \
                         map(int, entry['day_range'].split('-')[1].replace('Day ', '').split('-')[0])
            milan_actual += end - start + 1
    if milan_actual != milan_days:
        return {"error": "Milan days constraint not met"}
    
    # Check Seville show days
    seville_show_ok = False
    for entry in itinerary:
        if 'place' in entry and entry['place'] == 'Seville':
            start, end = map(int, entry['day_range'].split('-')[0].replace('Day ', '').split('-')[0]), \
                         map(int, entry['day_range'].split('-')[1].replace('Day ', '').split('-')[0])
            if start <= seville_show_start and end >= seville_show_end:
                seville_show_ok = True
    if not seville_show_ok:
        return {"error": "Seville show days constraint not met"}
    
    return itinerary

# Execute the planning
itinerary = plan_trip()

# Output as JSON
print(json.dumps(itinerary, indent=2))