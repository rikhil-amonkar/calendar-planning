import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 12
    city_days = {
        'Prague': 2,
        'Berlin': 3,
        'Tallinn': 5,
        'Stockholm': 5
    }
    
    # Conference constraints (days 6 and 8 must be in Berlin)
    conference_days = {6, 8}
    
    # Relative visit constraints (days 8-11 must be in Tallinn)
    relatives_days = {8, 9, 10, 11}
    
    # Direct flight connections
    connections = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Stockholm': ['Tallinn', 'Prague', 'Berlin']
    }
    
    # Generate all possible city orders
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all cities are connected in the order
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Initialize day tracking
        itinerary = []
        remaining_days = city_days.copy()
        current_day = 1
        
        # Try to assign cities in this order
        for city in order:
            if current_day > total_days:
                break
            
            # Determine how many days to spend in this city
            days_to_spend = remaining_days[city]
            
            # Special handling for Berlin and Tallinn
            if city == 'Berlin':
                # Must include conference days (6 and 8)
                # But day 8 is also in Tallinn for relatives - conflict!
                # Therefore Berlin must be before Tallinn
                # And must cover day 6
                if 6 not in range(current_day, current_day + days_to_spend):
                    # Adjust to include day 6
                    if 6 < current_day:
                        # Too late, can't cover day 6
                        break
                    days_to_spend = 6 - current_day + 1
            
            elif city == 'Tallinn':
                # Must cover days 8-11
                required_days = set(range(current_day, current_day + days_to_spend)) & relatives_days
                if relatives_days - required_days:
                    # Need to adjust to cover all relative days
                    if current_day > min(relatives_days):
                        # Started too late
                        break
                    # Make sure we cover all relative days
                    days_to_spend = max(relatives_days) - current_day + 1
            
            # Don't exceed total days
            if current_day + days_to_spend - 1 > total_days:
                days_to_spend = total_days - current_day + 1
            
            if days_to_spend <= 0:
                break
            
            # Add to itinerary
            end_day = current_day + days_to_spend - 1
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            remaining_days[city] -= days_to_spend
            current_day = end_day + 1
        
        # Check if we used all days and met all requirements
        if current_day == total_days + 1 and all(v == 0 for v in remaining_days.values()):
            # Verify all constraints are met
            berlin_days = set()
            tallinn_days = set()
            for entry in itinerary:
                start = int(entry['day_range'].split('-')[0].split(' ')[1])
                end = int(entry['day_range'].split('-')[1])
                days = set(range(start, end + 1))
                if entry['place'] == 'Berlin':
                    berlin_days.update(days)
                elif entry['place'] == 'Tallinn':
                    tallinn_days.update(days)
            
            if (conference_days.issubset(berlin_days) and (relatives_days.issubset(tallinn_days)):
                valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        return {"itinerary": []}
    
    # Select the first valid itinerary
    return {"itinerary": valid_itineraries[0]}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))