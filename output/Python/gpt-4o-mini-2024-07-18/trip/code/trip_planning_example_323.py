import json

def plan_trip():
    # Define the trip parameters
    total_days = 16
    stay_split = 5
    show_days_split = (7, 11) # Days from 7 to 11 in Split
    stay_oslo = 2
    stay_london = 7
    stay_porto = 5

    # Create a schedule list to hold the itinerary
    itinerary = []
    
    # Day 1-7: Stay in London
    itinerary.append({'day_range': 'Day 1-7', 'place': 'London'})
    
    # Day 7-11: Stay in Split (for the annual show)
    itinerary.append({'flying': 'Day 7-7', 'from': 'London', 'to': 'Split'})
    itinerary.append({'day_range': 'Day 7-11', 'place': 'Split'})

    # Day 11-12: Fly from Split to Oslo
    itinerary.append({'flying': 'Day 11-11', 'from': 'Split', 'to': 'Oslo'})
    itinerary.append({'day_range': 'Day 11-12', 'place': 'Oslo'})

    # Day 12-14: Fly from Oslo to Porto
    itinerary.append({'flying': 'Day 12-12', 'from': 'Oslo', 'to': 'Porto'})
    itinerary.append({'day_range': 'Day 12-16', 'place': 'Porto'})

    # Return the output in JSON format
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)