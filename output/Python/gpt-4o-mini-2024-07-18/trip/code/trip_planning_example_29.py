import json

def plan_trip():
    # Input parameters
    total_days = 10
    krakow_days = 2
    dubrovnik_days = 7
    frankfurt_days = 3
    
    # Days designation
    trip_plan = []

    # Calculate the non-wedding days
    days_before_wedding = total_days - 1  # because we have the wedding on day 9 and 10
    days_for_cities = days_before_wedding - (krakow_days + dubrovnik_days)
    
    # If we're to visit Frankfurt for a total of 3 days, then:
    # We'll be in Dubrovnik for 7 days, and Krakow for 2 days
    # This fits within our total days since:
    # Total days = Days in Dubrovnik (7) + Days in Frankfurt (3) + Days in Krakow (2)

    # Plan the itinerary
    current_day = 1

    # Stay in Dubrovnik first
    if dubrovnik_days > 0:
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + dubrovnik_days - 1}', 'place': 'Dubrovnik'})
        current_day += dubrovnik_days
    
    # Travel from Dubrovnik to Frankfurt
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dubrovnik', 'to': 'Frankfurt'})
    
    # Stay in Frankfurt
    if frankfurt_days > 0:
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + frankfurt_days - 1}', 'place': 'Frankfurt'})
        current_day += frankfurt_days
    
    # Travel from Frankfurt to Krakow
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Frankfurt', 'to': 'Krakow'})
    
    # Stay in Krakow
    if krakow_days > 0:
        trip_plan.append({'day_range': f'Day {current_day}-{current_day + krakow_days - 1}', 'place': 'Krakow'})
    
    # Final output as JSON
    return json.dumps(trip_plan, indent=4)

# Output the trip plan
if __name__ == "__main__":
    itinerary = plan_trip()
    print(itinerary)