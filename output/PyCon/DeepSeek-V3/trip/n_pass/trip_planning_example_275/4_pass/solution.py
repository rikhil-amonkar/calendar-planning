import json
from itertools import permutations

def main():
    # Cities and their required days
    cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
    required_days = {
        'Split': 5,
        'Vilnius': 4,
        'Santorini': 2,
        'Madrid': 6
    }
    
    # Direct flight connections
    connections = {
        'Vilnius': ['Split'],
        'Split': ['Vilnius', 'Madrid'],
        'Madrid': ['Split', 'Santorini'],
        'Santorini': ['Madrid']
    }
    
    # Total days
    total_days = 14
    
    # Conference constraint: Must be in Santorini on days 13 and 14
    conference_days = [13, 14]
    
    # Helper function to check if two cities are connected
    def are_connected(city1, city2):
        return city2 in connections.get(city1, [])
    
    # Function to check if a visit order has valid flight connections
    def has_valid_flights(order):
        for i in range(len(order) - 1):
            if not are_connected(order[i], order[i+1]):
                return False
        return True
    
    # Function to generate a valid itinerary for a given order
    def generate_itinerary(order):
        santorini_index = order.index('Santorini')
        
        # Santorini must cover days 13-14, so it must end on day 14
        # Therefore, it must start on day 13 (since it needs 2 days)
        santorini_start = 13
        santorini_end = 14
        
        # Build itinerary
        itinerary = []
        current_day = 1
        
        # Process cities before Santorini
        for i in range(santorini_index):
            city = order[i]
            days_needed = required_days[city]
            end_day = current_day + days_needed - 1
            
            # Check if this overlaps with Santorini
            if end_day >= santorini_start:
                return None  # Overlap, invalid
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
        
        # Add Santorini
        itinerary.append({
            'day_range': f"Day {santorini_start}-{santorini_end}",
            'place': 'Santorini'
        })
        
        # Process cities after Santorini
        next_day = santorini_end + 1
        for i in range(santorini_index + 1, len(order)):
            city = order[i]
            days_needed = required_days[city]
            end_day = next_day + days_needed - 1
            
            # Check if we exceed total days
            if end_day > total_days:
                return None  # Exceeds total days
            
            itinerary.append({
                'day_range': f"Day {next_day}-{end_day}",
                'place': city
            })
            next_day = end_day + 1
        
        # Check if we used exactly total_days
        if next_day - 1 == total_days:
            return itinerary
        else:
            return None
    
    # Try all possible permutations
    valid_itinerary = None
    
    for order in permutations(cities):
        # Check flight connections
        if not has_valid_flights(order):
            continue
        
        # Try to generate itinerary
        itinerary = generate_itinerary(order)
        if itinerary:
            valid_itinerary = itinerary
            break
    
    if valid_itinerary:
        result = {"itinerary": valid_itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()