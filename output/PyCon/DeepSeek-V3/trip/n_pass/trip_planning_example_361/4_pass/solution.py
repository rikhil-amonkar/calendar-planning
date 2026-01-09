import json

def main():
    total_days = 15
    
    # Fixed durations
    durations = {
        'Paris': 6,
        'Madrid': 7,
        'Bucharest': 2,
        'Seville': 3
    }
    
    # Flight routes
    flight_routes = {
        'Paris': ['Bucharest', 'Madrid', 'Seville'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Madrid must be days 1-7 (fixed)
    madrid_start = 1
    madrid_end = 7
    
    # Try different placements for other cities
    possible_orders = [
        # Try Madrid first, then other combinations
        ['Madrid', 'Paris', 'Seville', 'Bucharest'],
        ['Madrid', 'Paris', 'Bucharest', 'Seville'],
        ['Madrid', 'Seville', 'Paris', 'Bucharest'],
        ['Madrid', 'Seville', 'Bucharest', 'Paris'],
        ['Madrid', 'Bucharest', 'Paris', 'Seville'],
        ['Madrid', 'Bucharest', 'Seville', 'Paris'],
    ]
    
    def is_valid_order(order):
        # Check flight connectivity between consecutive cities
        for i in range(len(order) - 1):
            current = order[i]
            next_city = order[i + 1]
            if next_city not in flight_routes[current]:
                return False
        return True
    
    def calculate_schedule(order):
        schedule = {}
        current_day = 1
        
        for city in order:
            if city == 'Madrid':
                schedule['Madrid'] = (1, 7)  # Fixed
                current_day = 8  # Next available day after Madrid
            else:
                duration = durations[city]
                schedule[city] = (current_day, current_day + duration - 1)
                current_day += duration
        
        return schedule
    
    # Find a valid solution
    valid_schedule = None
    
    for order in possible_orders:
        if not is_valid_order(order):
            continue
            
        schedule = calculate_schedule(order)
        
        # Check if all cities fit within 15 days
        max_day = max(end for start, end in schedule.values())
        if max_day <= total_days:
            # Check Bucharest constraint (must include day 14 or 15)
            if 'Bucharest' in schedule:
                b_start, b_end = schedule['Bucharest']
                if 14 <= b_end <= 15 or 14 <= b_start <= 15:
                    valid_schedule = schedule
                    break
    
    if not valid_schedule:
        # Try a more flexible approach for Bucharest
        for order in possible_orders:
            if not is_valid_order(order):
                continue
                
            schedule = calculate_schedule(order)
            
            # Check if all cities fit within 15 days
            max_day = max(end for start, end in schedule.values())
            if max_day <= total_days:
                valid_schedule = schedule
                break
    
    if not valid_schedule:
        result = {"error": "No valid itinerary found with the given constraints"}
        print(json.dumps(result))
        return
    
    # Build itinerary
    itinerary = []
    for city in ['Madrid', 'Paris', 'Seville', 'Bucharest']:
        if city in valid_schedule:
            start, end = valid_schedule[city]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()