import json
from itertools import permutations

def main():
    # Define cities and their required days
    cities = {
        'Dublin': 5,
        'Krakow': 4,
        'Istanbul': 3,
        'Venice': 3,
        'Naples': 4,
        'Brussels': 2,
        'Mykonos': 4,
        'Frankfurt': 3
    }
    
    # Define direct flights as a graph
    flight_graph = {
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Istanbul', 'Frankfurt', 'Venice'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Istanbul', 'Frankfurt', 'Venice'],
        'Mykonos': ['Naples'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Brussels', 'Venice', 'Frankfurt'],
        'Venice': ['Istanbul', 'Frankfurt', 'Brussels', 'Naples', 'Dublin'],
        'Frankfurt': ['Krakow', 'Brussels', 'Istanbul', 'Venice', 'Naples', 'Dublin'],
        'Krakow': ['Frankfurt', 'Brussels', 'Istanbul', 'Dublin'],
        'Istanbul': ['Venice', 'Frankfurt', 'Naples', 'Brussels', 'Krakow', 'Dublin']
    }
    
    # Fixed constraints (must include these day ranges)
    fixed_constraints = {
        'Mykonos': (1, 4),    # Must include at least some days in 1-4
        'Dublin': (11, 15),   # Must include at least some days in 11-15
        'Istanbul': (9, 11),  # Must include at least some days in 9-11
        'Frankfurt': (15, 17) # Must include at least some days in 15-17
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll try different starting points (not just Mykonos first)
    possible_orders = []
    for start_city in ['Mykonos', 'Naples']:  # Mykonos can only be reached from Naples
        other_cities = [city for city in city_names if city != start_city]
        possible_orders.extend([(start_city,) + p for p in permutations(other_cities)])
    
    best_itinerary = None
    
    for order in possible_orders:
        # Initialize day assignments
        day_assignments = {}
        occupied_days = set()
        current_day = 1
        
        # Assign cities in order
        valid = True
        
        for i, city in enumerate(order):
            days_needed = cities[city]
            
            # Check fixed constraints for this city
            if city in fixed_constraints:
                fixed_start, fixed_end = fixed_constraints[city]
                # Find possible start days that satisfy the constraint
                possible_starts = []
                
                # Option 1: Start before fixed period and overlap
                earliest_start = max(current_day, fixed_start - days_needed + 1)
                latest_start = min(fixed_end, 21 - days_needed + 1)
                
                for start in range(earliest_start, latest_start + 1):
                    end = start + days_needed - 1
                    # Check if days are available
                    conflict = False
                    for day in range(start, end + 1):
                        if day in occupied_days:
                            conflict = True
                            break
                    if not conflict:
                        possible_starts.append(start)
                
                if not possible_starts:
                    valid = False
                    break
                
                # Choose the earliest possible start
                start = min(possible_starts)
                end = start + days_needed - 1
                day_assignments[city] = (start, end)
                occupied_days.update(range(start, end + 1))
                current_day = end + 1
            else:
                # No fixed constraints, assign to earliest available days
                start = current_day
                end = start + days_needed - 1
                if end > 21:
                    valid = False
                    break
                day_assignments[city] = (start, end)
                occupied_days.update(range(start, end + 1))
                current_day = end + 1
        
        if not valid:
            continue
        
        # Verify all cities are assigned
        if len(day_assignments) != len(cities):
            continue
        
        # Verify flight connections
        flight_valid = True
        for i in range(len(order) - 1):
            current_city = order[i]
            next_city = order[i + 1]
            if next_city not in flight_graph.get(current_city, []):
                flight_valid = False
                break
        
        if flight_valid:
            # Verify all constraints are met
            constraints_met = True
            for city, (fixed_start, fixed_end) in fixed_constraints.items():
                city_start, city_end = day_assignments[city]
                if not (city_start <= fixed_end and city_end >= fixed_start):
                    constraints_met = False
                    break
            
            if constraints_met:
                # Build itinerary in chronological order
                itinerary = []
                for city in order:
                    start, end = day_assignments[city]
                    itinerary.append({
                        'day_range': f"Day {start}-{end}",
                        'place': city
                    })
                
                # Sort by start day
                itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
                
                # Verify all 21 days are covered
                all_days = set()
                for item in itinerary:
                    start, end = map(int, item['day_range'].split(' ')[1].split('-'))
                    all_days.update(range(start, end + 1))
                
                if len(all_days) == 21:
                    best_itinerary = itinerary
                    break
    
    if best_itinerary:
        print(json.dumps({'itinerary': best_itinerary}))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == "__main__":
    main()