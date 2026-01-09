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
        # We need to place Santorini at the end to cover days 13-14
        if order[-1] != 'Santorini':
            return None
        
        itinerary = []
        current_day = 1
        
        # Process all cities except Santorini first
        for city in order[:-1]:
            days_needed = required_days[city]
            end_day = current_day + days_needed - 1
            
            # Check if we have enough days left for Santorini
            if end_day > 12:  # Need at least 2 days for Santorini at the end
                return None
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
        
        # Add Santorini at the end for conference days
        santorini_start = 13
        santorini_end = 14
        
        # Verify Santorini placement
        if santorini_start != current_day:
            return None
        
        itinerary.append({
            'day_range': f"Day {santorini_start}-{santorini_end}",
            'place': 'Santorini'
        })
        
        return itinerary
    
    # Try all possible permutations that end with Santorini
    valid_itinerary = None
    
    # Generate all permutations of the first three cities, with Santorini always last
    other_cities = [city for city in cities if city != 'Santorini']
    
    for first_three in permutations(other_cities):
        order = list(first_three) + ['Santorini']
        
        # Check flight connections
        if not has_valid_flights(order):
            continue
        
        # Try to generate itinerary
        itinerary = generate_itinerary(order)
        if itinerary:
            valid_itinerary = itinerary
            break
    
    if valid_itinerary:
        # Verify the itinerary meets all requirements
        total_used_days = 0
        santorini_correct = False
        
        for stay in valid_itinerary:
            city = stay['place']
            day_range = stay['day_range']
            start, end = map(int, day_range.replace('Day ', '').split('-'))
            days = end - start + 1
            
            # Check if days match requirement
            if days != required_days[city]:
                break
            
            # Check Santorini placement
            if city == 'Santorini':
                if start <= 13 and end >= 14:
                    santorini_correct = True
            
            total_used_days += days
        
        # Final verification
        if total_used_days == total_days and santorini_correct:
            result = {"itinerary": valid_itinerary}
            print(json.dumps(result, indent=2))
        else:
            print(json.dumps({"error": "No valid itinerary found"}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()