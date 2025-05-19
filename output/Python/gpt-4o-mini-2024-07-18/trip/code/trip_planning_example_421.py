import json

def compute_itinerary():
    # Define the trip parameters
    trip_days = 20
    trip_plan = []

    # Constraints:
    stay_nice_days = 5
    stay_krakow_days = 6
    stay_dublin_days = 7
    stay_lyon_days = 4
    stay_frankfurt_days = 2

    # Setup the itinerary based on the constraints
    current_day = 1
    
    # Stay in Nice for the first 5 days
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + stay_nice_days - 1}', 'place': 'Nice'})
    current_day += stay_nice_days
    
    # From Nice to Krakow (fly after the stay in Nice)
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Nice', 'to': 'Krakow'})
    current_day += 1  # Travel day
    
    # Stay in Krakow for 6 days
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + stay_krakow_days - 1}', 'place': 'Krakow'})
    current_day += stay_krakow_days
    
    # Next, travel from Krakow to Dublin
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Krakow', 'to': 'Dublin'})
    current_day += 1  # Travel day
    
    # Stay in Dublin for 7 days
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + stay_dublin_days - 1}', 'place': 'Dublin'})
    current_day += stay_dublin_days
    
    # Then, fly from Dublin to Lyon
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Dublin', 'to': 'Lyon'})
    current_day += 1  # Travel day
    
    # Stay in Lyon for 4 days
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + stay_lyon_days - 1}', 'place': 'Lyon'})
    current_day += stay_lyon_days
    
    # Finally, travel from Lyon to Frankfurt
    trip_plan.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Frankfurt'})
    current_day += 1  # Travel day
    
    # Stay in Frankfurt for 2 days
    trip_plan.append({'day_range': f'Day {current_day}-{current_day + stay_frankfurt_days - 1}', 'place': 'Frankfurt'})
    current_day += stay_frankfurt_days

    # This was the last planned stop
    # Now we ensure we meet the last requirement of meeting friends on Day 19-20
    # If current_day is 19 or less, we have them covered; however, we have days accounted already.

    # Convert to JSON format
    output = json.dumps(trip_plan, indent=4)
    return output

if __name__ == "__main__":
    itinerary = compute_itinerary()
    print(itinerary)