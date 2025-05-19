import json

def plan_trip():
    # Define the trip parameters
    total_days = 23
    stay_duration = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    relatives_in_oslo = (19, 23)
    conference_in_geneva = (1, 1)  # Conference on Day 1 and Day 7

    # Initialize the itinerary
    itinerary = []
    current_day = 1

    # Schedule Paris
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_duration["Paris"] - 1}', 'place': 'Paris'})
    current_day += stay_duration["Paris"]

    # Schedule Geneva
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Geneva'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_duration["Geneva"] - 1}', 'place': 'Geneva'})
    current_day += stay_duration["Geneva"]

    # Schedule Reykjavik
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Reykjavik'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_duration["Reykjavik"] - 1}', 'place': 'Reykjavik'})
    current_day += stay_duration["Reykjavik"]

    # Schedule Oslo (before relatives visit)
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Oslo'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_duration["Oslo"] - 1}', 'place': 'Oslo'})
    current_day += stay_duration["Oslo"]

    # Schedule Porto
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Porto'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_duration["Porto"] - 1}', 'place': 'Porto'})
    current_day += stay_duration["Porto"]

    # Return to Geneva for conference
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Porto', 'to': 'Geneva'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Geneva'})  # 2 days for conference
    current_day += 2

    # Schedule Oslo again for relatives
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Oslo'})
    itinerary.append({'day_range': f'Day {current_day}-{relatives_in_oslo[1]}', 'place': 'Oslo'})  # stay until Day 23

    # Output the itinerary as a JSON formatted dictionary
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)