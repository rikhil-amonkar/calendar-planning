import json

def plan_trip():
    # Define trip constraints
    total_days = 7
    days_madrid = 4
    days_dublin = 3
    days_tallinn = 2
    workshop_days = (6, 7)  # inclusive

    # Check the feasibility of the itinerary
    total_spent_days = days_madrid + days_dublin + days_tallinn
    if total_spent_days != total_days:
        raise ValueError("The days allocated to cities do not sum up to total days.")

    # Create the itinerary based on the constraints
    itinerary = []

    # Day 1 to Day 4 in Madrid
    itinerary.append({'day_range': 'Day 1-4', 'place': 'Madrid'})

    # Day 5 flying to Dublin
    itinerary.append({'flying': 'Day 5-5', 'from': 'Madrid', 'to': 'Dublin'})

    # Day 5 to Day 7 in Dublin
    itinerary.append({'day_range': 'Day 5-5', 'place': 'Dublin'})
    
    # Day 6 to Day 7 is workshop in Tallinn
    # Day 6 flying to Tallinn from Dublin
    itinerary.append({'flying': 'Day 6-6', 'from': 'Dublin', 'to': 'Tallinn'})
    
    # Day 6 to Day 7 in Tallinn
    itinerary.append({'day_range': 'Day 6-7', 'place': 'Tallinn'})
    
    # Convert itinerary to JSON format
    return json.dumps(itinerary, indent=4)

# Output the trip plan in JSON format
print(plan_trip())