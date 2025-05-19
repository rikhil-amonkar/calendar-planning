import json

def plan_trip():
    # Input Parameters
    total_days = 7
    riga_days = 2
    amsterdam_days = 2
    mykonos_days = total_days - (riga_days + amsterdam_days)  # Remaining days
    
    if mykonos_days < 0:
        raise ValueError("The allocated days exceed the total available days.")
    
    # Planning the itinerary
    itinerary = []

    # Day 1 and 2 in Riga
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Riga'})
    itinerary.append({'flying': 'Day 2-2', 'from': 'Riga', 'to': 'Amsterdam'})
    
    # Day 3 and 4 in Amsterdam
    itinerary.append({'day_range': 'Day 3-4', 'place': 'Amsterdam'})
    itinerary.append({'flying': 'Day 4-5', 'from': 'Amsterdam', 'to': 'Mykonos'})
    
    # Day 5 to 7 in Mykonos
    itinerary.append({'day_range': 'Day 5-7', 'place': 'Mykonos'})
    
    # Convert to JSON
    itinerary_json = json.dumps(itinerary, indent=2)
    
    return itinerary_json

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)