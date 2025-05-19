import json

def calculate_itinerary():
    # Input parameters
    total_days = 15
    cities = {
        'Stuttgart': {'duration': 5, 'workshop': (11, 15)},
        'Manchester': {'duration': 7, 'wedding': (1, 7)},
        'Madrid': {'duration': 4},
        'Vienna': {'duration': 2}
    }
    
    direct_flights = {
        'Vienna': ['Stuttgart', 'Manchester', 'Madrid'],
        'Stuttgart': ['Vienna', 'Manchester'],
        'Manchester': ['Vienna', 'Stuttgart', 'Madrid'],
        'Madrid': ['Vienna', 'Manchester']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Fixed events
    # Wedding in Manchester from day 1 to 7
    itinerary.append({'day_range': f'Day 1-7', 'place': 'Manchester'})
    current_day = 8
    last_city = 'Manchester'
    
    # Next, we need to fit Stuttgart workshop (must be between day 11-15)
    # Since current_day is 8 after Manchester, we have days 8-10 to fit other cities before Stuttgart
    
    # Possible cities to visit between Manchester and Stuttgart: Vienna or Madrid (since direct flights exist)
    # We have 3 days (8-10) before Stuttgart must start by day 11
    
    # Try to fit Vienna (2 days) and Madrid (4 days)
    # Since we have only 3 days, we can only fit Vienna (2 days) and leave 1 day for travel or adjust
    
    # Option 1: Go to Vienna for 2 days (days 8-9), then to Stuttgart (must start by day 11)
    # Flight from Manchester to Vienna is possible
    if 'Vienna' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Vienna'})
        itinerary.append({'day_range': f'Day {current_day}-{current_day + cities["Vienna"]["duration"] - 1}', 'place': 'Vienna'})
        current_day += cities["Vienna"]["duration"]
        last_city = 'Vienna'
    
    # Now, we need to go to Stuttgart (must be there by day 11)
    # Current_day is 10 after Vienna (8-9), so we can fly to Stuttgart on day 10
    if 'Stuttgart' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Stuttgart'})
        # Stuttgart must be from day 11-15, but we have day 10 now
        # So we stay in Stuttgart from day 10-14 (5 days)
        itinerary.append({'day_range': f'Day {current_day}-{current_day + cities["Stuttgart"]["duration"] - 1}', 'place': 'Stuttgart'})
        current_day += cities["Stuttgart"]["duration"]
        last_city = 'Stuttgart'
    
    # Check if all days are accounted for
    if current_day > total_days:
        # Adjust if needed (though in this case it fits)
        pass
    
    # Now, check if Madrid is visited
    # Madrid hasn't been visited yet, and we have no days left, so this plan doesn't work
    
    # Alternative plan: Go to Madrid first from Manchester
    # Reset itinerary
    itinerary = []
    itinerary.append({'day_range': f'Day 1-7', 'place': 'Manchester'})
    current_day = 8
    last_city = 'Manchester'
    
    # Try Madrid for 4 days (but we only have 3 days before Stuttgart)
    # Not possible
    
    # Another option: Go to Stuttgart directly from Manchester after wedding
    if 'Stuttgart' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Stuttgart'})
        # Stay in Stuttgart from day 8-12 (5 days)
        itinerary.append({'day_range': f'Day {current_day}-{current_day + cities["Stuttgart"]["duration"] - 1}', 'place': 'Stuttgart'})
        current_day += cities["Stuttgart"]["duration"]
        last_city = 'Stuttgart'
    
    # Now, we have days 13-15 left (3 days)
    # Need to fit Vienna (2 days) and Madrid (4 days)
    # Can only fit Vienna
    if 'Vienna' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Vienna'})
        itinerary.append({'day_range': f'Day {current_day}-{current_day + cities["Vienna"]["duration"] - 1}', 'place': 'Vienna'})
        current_day += cities["Vienna"]["duration"]
        last_city = 'Vienna'
    
    # Now, we have day 15 left, but Madrid requires 4 days - not possible
    # So Madrid cannot be visited in this plan
    
    # Final check: If Madrid is not visited, try to fit it somewhere else
    # Reset and try another approach
    itinerary = []
    itinerary.append({'day_range': f'Day 1-7', 'place': 'Manchester'})
    current_day = 8
    last_city = 'Manchester'
    
    # Go to Madrid first (but need 4 days, and Stuttgart must start by day 11)
    if 'Madrid' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Madrid'})
        # Stay in Madrid for 3 days (8-10) to reach Stuttgart by day 11
        adjusted_madrid_days = min(cities["Madrid"]["duration"], 11 - current_day)
        itinerary.append({'day_range': f'Day {current_day}-{current_day + adjusted_madrid_days - 1}', 'place': 'Madrid'})
        current_day += adjusted_madrid_days
        last_city = 'Madrid'
    
    # Now, fly to Stuttgart by day 11
    if 'Stuttgart' in direct_flights[last_city]:
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Stuttgart'})
        # Stay in Stuttgart for 5 days (11-15)
        stuttgart_start = max(current_day, 11)
        stuttgart_end = stuttgart_start + cities["Stuttgart"]["duration"] - 1
        if stuttgart_end > total_days:
            stuttgart_end = total_days
        itinerary.append({'day_range': f'Day {stuttgart_start}-{stuttgart_end}', 'place': 'Stuttgart'})
        current_day = stuttgart_end + 1
        last_city = 'Stuttgart'
    
    # Now, check if Vienna is visited
    # Vienna not visited yet, but no days left
    
    # Since Madrid was only partially visited, this plan is not optimal
    
    # Final plan: Accept that Madrid cannot be fully visited, or adjust Vienna
    # Best possible plan is to visit Manchester, Stuttgart, and Vienna
    
    # Reset to the first working plan
    itinerary = []
    itinerary.append({'day_range': f'Day 1-7', 'place': 'Manchester'})
    current_day = 8
    last_city = 'Manchester'
    
    # Fly to Vienna
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Vienna'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Vienna'})
    current_day += 2
    last_city = 'Vienna'
    
    # Fly to Stuttgart
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': last_city, 'to': 'Stuttgart'})
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Stuttgart'})
    current_day += 5
    
    # Output the itinerary
    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))