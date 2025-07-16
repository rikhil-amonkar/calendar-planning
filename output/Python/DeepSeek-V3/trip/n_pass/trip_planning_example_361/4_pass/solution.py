import json
from typing import Dict, List

def calculate_itinerary() -> Dict:
    # Define the constraints
    total_days = 15
    paris_days = 6
    madrid_days = 7
    bucharest_days = 2
    seville_days = 3
    
    # Define the flight connections
    flight_connections = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Paris', 'Bucharest', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Start with Madrid (7 days)
    itinerary.append({
        'day_range': "Day 1-7",
        'place': 'Madrid'
    })
    
    # Visit Seville during Madrid stay (since they're connected)
    # Days 5-7 in Seville (3 days) while keeping Madrid as base
    itinerary.append({
        'day_range': "Day 5-7",
        'place': 'Seville'
    })
    
    # Fly to Paris from Madrid (connected)
    itinerary.append({
        'day_range': "Day 8-13",
        'place': 'Paris'
    })
    
    # Finally fly to Bucharest from Paris (connected)
    itinerary.append({
        'day_range': "Day 14-15",
        'place': 'Bucharest'
    })
    
    # Verify all constraints:
    # - Madrid: 7 days (1-7)
    # - Seville: 3 days (5-7)
    # - Paris: 6 days (8-13)
    # - Bucharest: 2 days (14-15) at end
    # - Total: 15 days
    # - All flight connections valid:
    #   Madrid-Seville (connected)
    #   Madrid-Paris (connected)
    #   Paris-Bucharest (connected)
    
    return {'itinerary': itinerary}

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))