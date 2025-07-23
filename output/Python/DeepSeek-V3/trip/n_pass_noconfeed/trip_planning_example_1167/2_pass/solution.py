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
    
    # Fixed constraints
    fixed_constraints = {
        'Mykonos': (1, 4),    # Must be days 1-4
        'Dublin': (11, 15),   # Must include days 11-15
        'Istanbul': (9, 11),  # Must include days 9-11
        'Frankfurt': (15, 17) # Must include days 15-17
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
        
        # Assign fixed constraints first
        valid = True
        for city, (start, end) in fixed_constraints.items():
            if city not in order:
                valid = False
                break
            required_days = cities[city]
            # Check if the fixed range can satisfy the required days
            fixed_range_days = end - start + 1
            if fixed_range_days < required_days:
                # Need to extend beyond fixed range
                extension_needed = required_days - fixed_range_days
                # Try to extend before start
                if start > 1 and (start - 1) not in occupied_days:
                    new_start = start - extension_needed
                    if new_start >= 1 and all(d not in occupied_days for d in range(new_start, start)):
                        start = new_start
                    else:
                        # Try to extend after end
                        if end < 21 and (end + 1) not in occupied_days:
                            new_end = end + extension_needed
                            if new_end <= 21 and all(d not in occupied_days for d in range(end + 1, new_end + 1)):
                                end = new_end
                            else:
                                valid = False
                                break
                        else:
                            valid = False
                            break
                else:
                    # Try to extend after end
                    if end < 21 and (end + 1) not in occupied_days:
                        new_end = end + extension_needed
                        if new_end <= 21 and all(d not in occupied_days for d in range(end + 1, new_end + 1)):
                            end = new_end
                        else:
                            valid = False
                            break
                    else:
                        valid = False
                        break
            
            day_assignments[city] = (start, end)
            occupied_days.update(range(start, end + 1))
        
        if not valid:
            continue
        
        # Assign remaining cities to available days
        remaining_cities = [city for city in order if city not in day_assignments]
        
        # Find available day blocks
        available_blocks = []
        current_block_start = None
        for day in range(1, 22):
            if day not in occupied_days:
                if current_block_start is None:
                    current_block_start = day
            else:
                if current_block_start is not None:
                    available_blocks.append((current_block_start, day - 1))
                    current_block_start = None
        if current_block_start is not None:
            available_blocks.append((current_block_start, 21))
        
        # Assign remaining cities to available blocks
        remaining_city_days = {city: cities[city] for city in remaining_cities}
        temp_assignments = {}
        
        for city in remaining_cities:
            days_needed = remaining_city_days[city]
            assigned = False
            for i, (block_start, block_end) in enumerate(available_blocks):
                block_length = block_end - block_start + 1
                if block_length >= days_needed:
                    # Assign to this block
                    temp_assignments[city] = (block_start, block_start + days_needed - 1)
                    # Update the block
                    if block_start + days_needed <= block_end:
                        available_blocks[i] = (block_start + days_needed, block_end)
                    else:
                        available_blocks.pop(i)
                    assigned = True
                    break
            if not assigned:
                valid = False
                break
        
        if not valid:
            continue
        
        # Merge all assignments
        all_assignments = {**day_assignments, **temp_assignments}
        
        # Build itinerary in chronological order
        itinerary = []
        for city in order:
            start, end = all_assignments[city]
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
        
        # Sort by start day
        itinerary.sort(key=lambda x: x['day_range'])
        
        # Check flight connections
        flight_valid = True
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if next_city not in flight_graph.get(current_city, []):
                flight_valid = False
                break
        
        if flight_valid:
            # Verify all cities are included and days are covered
            covered_days = set()
            included_cities = set()
            for entry in itinerary:
                start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
                covered_days.update(range(start, end + 1))
                included_cities.add(entry['place'])
            
            if len(covered_days) == 21 and included_cities == set(cities.keys()):
                best_itinerary = itinerary
                break  # Found a valid itinerary
    
    if best_itinerary:
        print(json.dumps({'itinerary': best_itinerary}))
    else:
        print(json.dumps({'error': 'No valid itinerary found'}))

if __name__ == "__main__":
    main()