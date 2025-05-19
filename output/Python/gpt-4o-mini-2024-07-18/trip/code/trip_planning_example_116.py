import json

def plan_trip():
    # Constants for the trip
    total_days = 18
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_days = [12, 18]  # Days we must be in Santorini for conference
    
    # Validate day allocation
    if split_days + santorini_days + london_days != total_days:
        raise ValueError("The days allocated to cities do not sum up to the total days.")
    
    itinerary = []
    current_day = 1

    # Days in Split
    itinerary.append({'day_range': f'Day {current_day}-{current_day + split_days - 1}', 'place': 'Split'})
    current_day += split_days

    # Flight from Split to Santorini
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Santorini'})
    
    # Days in Santorini before first conference
    itinerary.append({'day_range': f'Day {current_day}-{current_day + conference_days[0] - 1 - 1}', 'place': 'Santorini'})
    current_day += (conference_days[0] - 1)
    
    # Conference day in Santorini
    itinerary.append({'day_range': f'Day {current_day}', 'place': 'Santorini'})
    current_day += 1

    # Days in Santorini after first conference until the second
    days_to_allocate = santorini_days - 1  # Subtract the conference day already accounted for
    itinerary.append({'day_range': f'Day {current_day}-{current_day + days_to_allocate - 1}', 'place': 'Santorini'})
    current_day += days_to_allocate

    # Flight from Santorini to London
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Santorini', 'to': 'London'})
    
    # Days in London until the end of the trip
    itinerary.append({'day_range': f'Day {current_day}-{total_days}', 'place': 'London'})

    # Final output as JSON
    return json.dumps(itinerary, indent=4)

# Run the trip planning function and print the result
if __name__ == "__main__":
    print(plan_trip())