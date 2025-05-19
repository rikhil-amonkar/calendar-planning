import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    days_in_brussels = 2
    days_in_split = 5
    days_in_barcelona = 7
    
    # Flight connections
    connections = {
        'Brussels': ['Barcelona'],
        'Barcelona': ['Brussels', 'Split'],
        'Split': ['Barcelona']
    }
    
    # Validate total days
    if days_in_brussels + days_in_split + days_in_barcelona != total_days:
        raise ValueError("Total days in cities do not match the trip duration.")
    
    # Determine the itinerary based on constraints
    itinerary = []
    
    # Day 1-2: Brussels (conference)
    itinerary.append({'day_range': 'Day 1-2', 'place': 'Brussels'})
    
    # After conference, fly to Barcelona (Day 3)
    itinerary.append({'flying': 'Day 3-3', 'from': 'Brussels', 'to': 'Barcelona'})
    
    # Stay in Barcelona for part of the time
    barcelona_stay1 = 7 - (total_days - days_in_brussels - days_in_split)
    itinerary.append({'day_range': f'Day 3-{3 + barcelona_stay1 - 1}', 'place': 'Barcelona'})
    
    # Fly to Split (Day 3 + barcelona_stay1)
    fly_day = 3 + barcelona_stay1
    itinerary.append({'flying': f'Day {fly_day}-{fly_day}', 'from': 'Barcelona', 'to': 'Split'})
    
    # Stay in Split for 5 days
    itinerary.append({'day_range': f'Day {fly_day}-{fly_day + days_in_split - 1}', 'place': 'Split'})
    
    # Fly back to Barcelona (Day fly_day + days_in_split)
    fly_day_back = fly_day + days_in_split
    itinerary.append({'flying': f'Day {fly_day_back}-{fly_day_back}', 'from': 'Split', 'to': 'Barcelona'})
    
    # Stay in Barcelona for the remaining days
    remaining_barcelona_days = days_in_barcelona - barcelona_stay1
    itinerary.append({'day_range': f'Day {fly_day_back}-{fly_day_back + remaining_barcelona_days - 1}', 'place': 'Barcelona'})
    
    return itinerary

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))