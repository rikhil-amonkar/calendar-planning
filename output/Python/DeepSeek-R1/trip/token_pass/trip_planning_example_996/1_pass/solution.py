import json
from itertools import permutations

def main():
    # Cities and their required days
    cities = {
        'Mykonos': 3,
        'Prague': 3,
        'Valencia': 5,
        'Riga': 5,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }
    
    # Direct flights graph
    graph = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Zurich': ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Valencia', 'Riga'],
        'Prague': ['Bucharest', 'Zurich', 'Riga', 'Valencia'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Valencia': ['Bucharest', 'Zurich', 'Prague'],
        'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague']
    }
    
    # Fixed events
    fixed_events = [
        (1, 3, 'Mykonos'),
        (7, 9, 'Prague')
    ]
    
    total_days = 22
    n_cities = len(cities)
    
    # Generate all possible orders of cities
    city_list = list(cities.keys())
    best_itinerary = None
    min_violations = float('inf')
    
    for order in permutations(city_list):
        # Check if fixed events are in the order
        fixed_cities = [city for (start, end, city) in fixed_events]
        fixed_indices = [order.index(city) for city in fixed_cities]
        if fixed_indices != sorted(fixed_indices):
            continue
            
        # Calculate total travel days and validate direct flights
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in graph[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
            
        # Initialize day allocation
        days_spent = {city: 0 for city in cities}
        itinerary = []
        current_day = 1
        
        # Process fixed events first
        for start, end, city in fixed_events:
            # Add days before fixed event if needed
            if current_day < start:
                # Allocate days to cities before the fixed event
                prev_cities = order[:order.index(city)]
                for c in prev_cities:
                    if current_day >= start:
                        break
                    if days_spent[c] < cities[c]:
                        days_needed = min(cities[c] - days_spent[c], start - current_day)
                        itinerary.append((current_day, current_day + days_needed - 1, c))
                        days_spent[c] += days_needed
                        current_day += days_needed
            
            # Add fixed event
            event_days = end - start + 1
            itinerary.append((start, end, city))
            days_spent[city] += event_days
            current_day = end + 1
        
        # Add remaining cities after fixed events
        remaining_cities = order[order.index(fixed_events[-1][2]) + 1:]
        for city in remaining_cities:
            if current_day > total_days:
                break
            days_needed = cities[city] - days_spent.get(city, 0)
            if days_needed <= 0:
                continue
            end_day = current_day + days_needed - 1
            if end_day > total_days:
                end_day = total_days
                days_needed = end_day - current_day + 1
            itinerary.append((current_day, end_day, city))
            days_spent[city] += days_needed
            current_day = end_day + 1
        
        # Check if all days are allocated and requirements are met
        violations = 0
        for city, req in cities.items():
            if days_spent.get(city, 0) != req:
                violations += abs(days_spent.get(city, 0) - req)
        if current_day <= total_days:
            violations += total_days - current_day + 1
            
        if violations < min_violations:
            min_violations = violations
            best_itinerary = itinerary
    
    # Format the itinerary as JSON
    formatted_itinerary = []
    for start, end, city in best_itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        formatted_itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": formatted_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()