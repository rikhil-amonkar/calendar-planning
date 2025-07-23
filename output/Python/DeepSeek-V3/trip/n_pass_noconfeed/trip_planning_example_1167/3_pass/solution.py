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
    
    # Fixed constraints (must include these days)
    fixed_constraints = {
        'Mykonos': (1, 4),    # Must include at least some days in 1-4
        'Dublin': (11, 15),   # Must include at least some days in 11-15
        'Istanbul': (9, 11),  # Must include at least some days in 9-11
        'Frankfurt': (15, 17) # Must include at least some days in 15-17
    }
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll limit permutations to those starting with Mykonos (from fixed constraint)
    other_cities = [city for city in city_names if city != 'Mykonos']
    possible_orders = [('Mykonos',) + p for p in permutations(other_cities)]
    
    best_itinerary = None
    
    for order in possible_orders:
        # Initialize day assignments
        day_assignments = {}
        occupied_days = set()
        
        # Assign Mykonos first (must start with it)
        mykonos_days = cities['Mykonos']
        # Must overlap with days 1-4
        mykonos_start = max(1, 4 - mykonos_days + 1)
        mykonos_end = mykonos_start + mykonos_days - 1
        day_assignments['Mykonos'] = (mykonos_start, mykonos_end)
        occupied_days.update(range(mykonos_start, mykonos_end + 1))
        
        # Assign other cities with flexible constraints
        current_day = mykonos_end + 1
        valid = True
        
        for i in range(1, len(order)):
            city = order[i]
            days_needed = cities[city]
            
            # Check if this city has fixed constraints
            if city in fixed_constraints:
                fixed_start, fixed_end = fixed_constraints[city]
                # Find the earliest position that overlaps with fixed days
                start_options = []
                
                # Option 1: Start before fixed period and overlap
                if fixed_start - days_needed + 1 >= current_day:
                    start_options.append(fixed_start - days_needed + 1)
                
                # Option 2: Start during fixed period
                if fixed_start >= current_day:
                    start_options.append(fixed_start)
                
                # Option 3: Start after fixed period (but must still overlap)
                if fixed_end + 1 >= current_day and fixed_end + days_needed - 1 <= 21:
                    start_options.append(fixed_end + 1)
                
                if not start_options:
                    valid = False
                    break
                
                # Try each option in order
                assigned = False
                for start in sorted(start_options):
                    end = start + days_needed - 1
                    if end > 21:
                        continue
                    # Check if days are available
                    conflict = False
                    for day in range(start, end + 1):
                        if day in occupied_days:
                            conflict = True
                            break
                    if not conflict:
                        day_assignments[city] = (start, end)
                        occupied_days.update(range(start, end + 1))
                        current_day = end + 1
                        assigned = True
                        break
                
                if not assigned:
                    valid = False
                    break
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
        
        # Verify all days are covered (1-21)
        if len(occupied_days) != 21:
            # Fill any gaps with the last city's extension
            last_city = order[-1]
            last_start, last_end = day_assignments[last_city]
            needed_extension = 21 - last_end
            if needed_extension > 0 and last_start - needed_extension >= 1:
                new_start = last_start - needed_extension
                # Check if these days are available
                conflict = False
                for day in range(new_start, last_start):
                    if day in occupied_days:
                        conflict = True
                        break
                if not conflict:
                    day_assignments[last_city] = (new_start, last_end)
                    occupied_days.update(range(new_start, last_start))
        
        # Verify flight connections
        flight_valid = True
        for i in range(len(order) - 1):
            current_city = order[i]
            next_city = order[i + 1]
            if next_city not in flight_graph.get(current_city, []):
                flight_valid = False
                break
        
        if flight_valid:
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
            
            # Verify all constraints are met
            constraints_met = True
            for city, (fixed_start, fixed_end) in fixed_constraints.items():
                city_start, city_end = day_assignments[city]
                if not (city_start <= fixed_end and city_end >= fixed_start):
                    constraints_met = False
                    break
            
            if constraints_met:
                best_itinerary = itinerary
                break
    
    if best_itinerary:
        print(json.dumps({'itinerary': best_itinerary}))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == "__main__":
    main()