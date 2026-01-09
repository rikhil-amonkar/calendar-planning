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
        # Try all possible placements of Santorini that cover days 13-14
        santorini_index = order.index('Santorini')
        
        # Try different start days for Santorini that ensure it covers days 13-14
        for santorini_start in range(13 - required_days['Santorini'] + 1, 14):
            santorini_end = santorini_start + required_days['Santorini'] - 1
            
            # Santorini must cover both days 13 and 14
            if santorini_start > 13 or santorini_end < 14:
                continue
            
            itinerary = []
            current_day = 1
            
            # Process cities before Santorini
            for i in range(santorini_index):
                city = order[i]
                days_needed = required_days[city]
                end_day = current_day + days_needed - 1
                
                # Check if this overlaps with Santorini
                if end_day >= santorini_start:
                    break
                
                itinerary.append({
                    'day_range': f"Day {current_day}-{end_day}",
                    'place': city
                })
                current_day = end_day + 1
            
            # If we successfully processed all cities before Santorini
            if len(itinerary) == santorini_index:
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
                        break
                    
                    itinerary.append({
                        'day_range': f"Day {next_day}-{end_day}",
                        'place': city
                    })
                    next_day = end_day + 1
                
                # Check if we used all cities and total days
                if (len(itinerary) == len(cities) and 
                    next_day - 1 == total_days):
                    return itinerary
        
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
        # Verify the itinerary meets all requirements
        total_used_days = 0
        santorini_correct = False
        cities_visited = set()
        
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
            
            cities_visited.add(city)
            total_used_days += days
        
        # Final verification
        if (total_used_days == total_days and 
            santorini_correct and 
            len(cities_visited) == len(cities)):
            result = {"itinerary": valid_itinerary}
            print(json.dumps(result, indent=2))
        else:
            print(json.dumps({"error": "No valid itinerary found"}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()