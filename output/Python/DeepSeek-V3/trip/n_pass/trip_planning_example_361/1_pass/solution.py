import json
from typing import List, Dict

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
    
    # Madrid has a fixed show from day 1 to day 7
    madrid_start_day = 1
    madrid_end_day = 7
    itinerary.append({
        'day_range': f"Day {madrid_start_day}-{madrid_end_day}",
        'place': 'Madrid'
    })
    
    # After Madrid, we have days 8-15 left (8 days)
    remaining_days = total_days - madrid_end_day
    
    # Bucharest must be visited between day 14 and 15 (i.e., day 14-15)
    bucharest_start_day = 14
    bucharest_end_day = 15
    # Check if Bucharest can be reached from Madrid
    current_city = 'Madrid'
    if 'Bucharest' in flight_connections[current_city]:
        # We can go directly from Madrid to Bucharest, but we need to fit other cities
        pass
    else:
        raise ValueError("No direct flight from Madrid to Bucharest")
    
    # Seville needs 3 days, Paris needs 6 days
    # We have days 8-13 to fit Seville and Paris before Bucharest (days 14-15)
    # Possible options:
    # Option 1: Seville first, then Paris
    # Option 2: Paris first, then Seville
    
    # Check flight connections for both options
    
    # Option 1: Madrid -> Seville -> Paris -> Bucharest
    # Madrid to Seville: possible
    if 'Seville' in flight_connections['Madrid']:
        seville_start_day = 8
        seville_end_day = 10
        itinerary.append({
            'day_range': f"Day {seville_start_day}-{seville_end_day}",
            'place': 'Seville'
        })
        # Seville to Paris: possible
        if 'Paris' in flight_connections['Seville']:
            paris_start_day = 11
            paris_end_day = 16  # But we only have until day 15
            # Adjust Paris days to fit before Bucharest
            paris_end_day = 13
            if paris_end_day - paris_start_day + 1 == 3:  # Only 3 days, but we need 6
                # Not enough days, so this option doesn't work
                pass
            else:
                # Not enough days for Paris
                pass
        else:
            pass
    
    # Option 2: Madrid -> Paris -> Seville -> Bucharest
    # Madrid to Paris: possible
    if 'Paris' in flight_connections['Madrid']:
        paris_start_day = 8
        paris_end_day = 13  # 6 days
        itinerary.append({
            'day_range': f"Day {paris_start_day}-{paris_end_day}",
            'place': 'Paris'
        })
        # Paris to Seville: possible
        if 'Seville' in flight_connections['Paris']:
            seville_start_day = 14
            seville_end_day = 16  # But we only have until day 15
            # Adjust Seville days to fit before Bucharest
            seville_end_day = 15
            if seville_end_day - seville_start_day + 1 == 2:  # Only 2 days, but we need 3
                # Not enough days, so this option doesn't work
                pass
            else:
                # Not enough days for Seville
                pass
        else:
            pass
    
    # Option 3: Madrid -> Paris -> Bucharest -> Seville
    # But Bucharest must be last, so this doesn't work
    
    # Option 4: Madrid -> Bucharest -> ... but Bucharest must be last, so invalid
    
    # After evaluating, the only feasible option is:
    # Madrid (1-7), Paris (8-13), Bucharest (14-15)
    # But Seville is not visited, so we need to adjust
    
    # Alternative approach: include Seville in the middle
    # Madrid (1-7), Paris (8-10), Seville (11-13), Bucharest (14-15)
    # Check flight connections:
    # Madrid to Paris: yes
    # Paris to Seville: yes
    # Seville to Bucharest: no (no direct flight)
    # So this doesn't work
    
    # Another option: Madrid (1-7), Seville (8-10), Paris (11-16) but only until 15
    # Paris would be 11-15 (5 days), but we need 6
    
    # Final feasible option: Madrid (1-7), Paris (8-13), Bucharest (14-15)
    # Seville is not visited, but constraints cannot be fully satisfied
    # Adjust Seville to be visited for 1 day overlapping with Paris or Madrid
    
    # Since all constraints cannot be satisfied, we prioritize:
    # Madrid (1-7), Bucharest (14-15), Paris and Seville must fit in 8-13
    # Paris needs 6, Seville needs 3, but only 6 days available
    # Not possible, so we reduce Paris or Seville days
    
    # Given the strict constraints, the only possible itinerary is:
    itinerary = [
        {'day_range': 'Day 1-7', 'place': 'Madrid'},
        {'day_range': 'Day 8-13', 'place': 'Paris'},
        {'day_range': 'Day 14-15', 'place': 'Bucharest'}
    ]
    # Seville is not visited due to time constraints
    
    return {'itinerary': itinerary}

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary))