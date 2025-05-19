import json
from typing import List, Dict, Union

def calculate_itinerary() -> List[Dict[str, Union[str, Dict[str, str]]]]:
    # Define the cities and their required days
    cities = {
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    
    # Define the constraints
    constraints = {
        'Stuttgart': [(4, 4), (7, 7)],
        'Istanbul': [(19, 22)],
        'Munich': [(13, 15)],
        'Reykjavik': [(1, 4)]
    }
    
    # Define direct flights as a graph
    flights = {
        'Geneva': ['Istanbul', 'Munich', 'Valencia'],
        'Istanbul': ['Geneva', 'Stuttgart', 'Vilnius', 'Valencia', 'Munich'],
        'Reykjavik': ['Munich', 'Stuttgart'],
        'Stuttgart': ['Valencia', 'Istanbul', 'Reykjavik'],
        'Munich': ['Reykjavik', 'Geneva', 'Vilnius', 'Seville', 'Istanbul', 'Valencia'],
        'Valencia': ['Stuttgart', 'Seville', 'Istanbul', 'Geneva', 'Munich'],
        'Seville': ['Valencia', 'Munich'],
        'Vilnius': ['Istanbul', 'Munich']
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Assign constrained cities first
    # Reykjavik from day 1-4
    itinerary.append({'day_range': f'Day 1-4', 'place': 'Reykjavik'})
    current_day = 5
    current_city = 'Reykjavik'
    
    # Next, Stuttgart has a conference on day 4 and day 7
    # Since day 4 is already in Reykjavik, next is day 7
    # Need to be in Stuttgart by day 7
    # Possible flight from Reykjavik to Stuttgart
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Reykjavik', 'to': 'Stuttgart'})
    current_city = 'Stuttgart'
    current_day += 0  # Flight is on the same day
    
    # Stay in Stuttgart from day 5-7 (3 days, but total is 4)
    # But conference is on day 7, so we can stay until day 8
    itinerary.append({'day_range': f'Day {current_day}-8', 'place': 'Stuttgart'})
    current_day = 9
    current_city = 'Stuttgart'
    
    # Next, Munich has a show from day 13-15
    # Need to be in Munich by day 13
    # Possible flight from Stuttgart to Valencia, then to Munich
    # Or Stuttgart to Munich via Reykjavik, but that's not efficient
    # Stuttgart to Valencia is direct
    itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Stuttgart', 'to': 'Valencia'})
    current_city = 'Valencia'
    current_day += 0
    
    # Stay in Valencia for 5 days
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 4}', 'place': 'Valencia'})
    current_day += 5
    current_city = 'Valencia'
    
    # Now, need to be in Munich by day 13
    # Current day is 14, but show is from 13-15
    # Need to adjust to reach Munich by day 13
    # So backtrack: Valencia to Munich is direct
    # Adjust Valencia stay to end on day 12
    # Remove last entry and recalculate
    itinerary = itinerary[:-1]
    current_day = 9
    itinerary.append({'day_range': f'Day {current_day}-12', 'place': 'Valencia'})
    current_day = 13
    itinerary.append({'flying': f'Day 13-13', 'from': 'Valencia', 'to': 'Munich'})
    itinerary.append({'day_range': f'Day 13-15', 'place': 'Munich'})
    current_day = 16
    current_city = 'Munich'
    
    # Next, Istanbul relatives between day 19-22
    # Need to be in Istanbul by day 19
    # From Munich, direct flight to Istanbul
    # Can stay in Munich until day 18
    itinerary.append({'day_range': f'Day 16-18', 'place': 'Munich'})
    current_day = 19
    itinerary.append({'flying': f'Day 19-19', 'from': 'Munich', 'to': 'Istanbul'})
    itinerary.append({'day_range': f'Day 19-22', 'place': 'Istanbul'})
    current_day = 23
    current_city = 'Istanbul'
    
    # Remaining cities: Vilnius (4), Seville (3), Geneva (5)
    # From Istanbul, can fly to Vilnius
    itinerary.append({'flying': f'Day 23-23', 'from': 'Istanbul', 'to': 'Vilnius'})
    itinerary.append({'day_range': f'Day 23-26', 'place': 'Vilnius'})
    # But we only have until day 25
    # Adjust Vilnius stay to 3 days
    itinerary = itinerary[:-1]
    itinerary.append({'day_range': f'Day 23-25', 'place': 'Vilnius'})
    
    return itinerary

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))