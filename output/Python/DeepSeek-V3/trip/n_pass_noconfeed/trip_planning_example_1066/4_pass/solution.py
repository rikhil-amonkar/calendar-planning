import json

def find_itinerary():
    # Cities and required days
    cities = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Special constraints
    conference_days = (20, 21)  # Madrid must be on these days
    stuttgart_friend_days = (1, 4)  # Stuttgart must include these days
    
    # Direct flights (bidirectional)
    flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Helsinki', 'Madrid'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    # Fix typo in Helsinki spelling
    flights['Helsinki'] = flights.pop('Helsinki')
    
    # Strategic approach:
    # 1. Place Stuttgart first (days 1-4)
    # 2. Place Madrid last (days 20-21)
    # 3. Fill in the remaining cities in between
    
    # Initialize itinerary with Stuttgart
    itinerary = [
        {'day_range': "Day 1-4", 'place': 'Stuttgart'}
    ]
    current_day = 5
    
    # Next possible cities from Stuttgart: London or Split
    # Let's try Split next (3 days)
    if current_day + 3 - 1 <= 19:  # Must end before Madrid
        itinerary.append({'day_range': f"Day {current_day}-{current_day+2}", 'place': 'Split'})
        current_day += 3
    
    # From Split, possible next: Madrid, Helsinki, London, Stuttgart
    # Can't go to Madrid yet (must be last), Stuttgart already visited
    # Try Helsinki (5 days)
    if current_day + 5 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+4}", 'place': 'Helsinki'})
        current_day += 5
    
    # From Helsinki, possible next: London, Madrid, Brussels, Split
    # Try Brussels (4 days)
    if current_day + 4 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+3}", 'place': 'Brussels'})
        current_day += 4
    
    # From Brussels, possible next: London, Bucharest, Helsinki, Madrid
    # Try Bucharest (3 days)
    if current_day + 3 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+2}", 'place': 'Bucharest'})
        current_day += 3
    
    # From Bucharest, possible next: London, Brussels, Madrid
    # Try London (5 days)
    if current_day + 5 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+4}", 'place': 'London'})
        current_day += 5
    
    # From London, possible next: many options, but we need to place Mykonos (2 days)
    if current_day + 2 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+1}", 'place': 'Mykonos'})
        current_day += 2
    
    # Finally place Madrid (must be days 20-21)
    if current_day == 20:
        itinerary.append({'day_range': "Day 20-21", 'place': 'Madrid'})
    
    # Verify we've included all cities
    included_cities = {item['place'] for item in itinerary}
    if included_cities == set(cities.keys()) and len(itinerary) == len(cities):
        return {'itinerary': itinerary}
    
    # If the above path didn't work, try a different order
    # Alternative path: Stuttgart -> London -> ...
    itinerary = [
        {'day_range': "Day 1-4", 'place': 'Stuttgart'}
    ]
    current_day = 5
    
    # From Stuttgart to London (5 days)
    if current_day + 5 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+4}", 'place': 'London'})
        current_day += 5
    
    # From London to Brussels (4 days)
    if current_day + 4 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+3}", 'place': 'Brussels'})
        current_day += 4
    
    # From Brussels to Bucharest (3 days)
    if current_day + 3 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+2}", 'place': 'Bucharest'})
        current_day += 3
    
    # From Bucharest to Madrid (but Madrid must be last)
    # Instead go to Split (3 days)
    if current_day + 3 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+2}", 'place': 'Split'})
        current_day += 3
    
    # From Split to Helsinki (5 days)
    if current_day + 5 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+4}", 'place': 'Helsinki'})
        current_day += 5
    
    # Place Mykonos (2 days)
    if current_day + 2 - 1 <= 19:
        itinerary.append({'day_range': f"Day {current_day}-{current_day+1}", 'place': 'Mykonos'})
        current_day += 2
    
    # Finally place Madrid (must be days 20-21)
    if current_day == 20:
        itinerary.append({'day_range': "Day 20-21", 'place': 'Madrid'})
    
    # Verify we've included all cities
    included_cities = {item['place'] for item in itinerary}
    if included_cities == set(cities.keys()) and len(itinerary) == len(cities):
        return {'itinerary': itinerary}
    
    # If no valid itinerary found
    return {'itinerary': []}

# Execute and print result
result = find_itinerary()
print(json.dumps(result, indent=2))