import json

def plan_trip():
    # Define the constraints and parameters
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7

    # Total days allocated
    allocated_days = brussels_days + split_days + barcelona_days
    
    if allocated_days != total_days:
        raise ValueError("The sum of allocated days does not equal total trip days.")
    
    itinerary = []

    # Brussels for first 2 days at conference
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Brussels'})

    # Travel to Barcelona from Brussels (Day 2 end)
    itinerary.append({'flying': 'Day 2-2', 'from': 'Brussels', 'to': 'Barcelona'})

    # Barcelona for the next 7 days
    itinerary.append({'day_range': 'Day 3-9', 'place': 'Barcelona'})

    # Travel to Split from Barcelona (Day 9 end)
    itinerary.append({'flying': 'Day 9-9', 'from': 'Barcelona', 'to': 'Split'})

    # Split for the next 5 days
    itinerary.append({'day_range': 'Day 10-12', 'place': 'Split'})
    
    return json.dumps(itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)