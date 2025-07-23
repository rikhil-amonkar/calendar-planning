import json
from itertools import permutations
from collections import defaultdict

def find_itinerary():
    # Cities and required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Constraints (city, start_day, end_day)
    constraints = [
        ('Brussels', 26, 27),  # Wedding in Brussels between day 26-27
        ('Vilnius', 20, 23),   # Friends in Vilnius between day 20-23
        ('Venice', 7, 11),     # Workshop in Venice between day 7-11
        ('Geneva', 1, 4)       # Relatives in Geneva between day 1-4
    ]
    
    # Direct flights (undirected graph)
    flights = {
        'Munich': ['Vienna', 'Madrid', 'Venice', 'Reykjavik', 'Istanbul', 'Brussels', 'Riga'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Venice', 'Riga', 'Geneva', 'Brussels', 'Madrid', 'Reykjavik'],
        'Istanbul': ['Brussels', 'Geneva', 'Vienna', 'Riga', 'Venice', 'Madrid', 'Vilnius', 'Munich'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Vilnius', 'Reykjavik', 'Madrid', 'Vienna', 'Geneva', 'Munich'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Brussels', 'Istanbul', 'Geneva', 'Reykjavik'],
        'Vilnius': ['Vienna', 'Brussels', 'Istanbul', 'Munich', 'Riga'],
        'Venice': ['Brussels', 'Munich', 'Vienna', 'Istanbul', 'Madrid'],
        'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
        'Riga': ['Brussels', 'Istanbul', 'Vienna', 'Munich', 'Vilnius'],
        'Reykjavik': ['Munich', 'Vienna', 'Brussels', 'Madrid']
    }
    
    # Fixed segments based on constraints
    fixed_segments = [
        {'place': 'Geneva', 'start': 1, 'end': 4},
        {'place': 'Venice', 'start': 7, 'end': 11},
        {'place': 'Vilnius', 'start': 20, 'end': 23},
        {'place': 'Brussels', 'start': 26, 'end': 27}
    ]
    
    # Remaining cities to schedule (excluding fixed segments)
    remaining_cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Madrid': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Create a day occupancy map
    day_occupancy = defaultdict(str)
    for seg in fixed_segments:
        for day in range(seg['start'], seg['end'] + 1):
            day_occupancy[day] = seg['place']
    
    # Find available time slots between fixed segments
    available_slots = []
    current_start = None
    
    for day in range(1, 28):
        if day not in day_occupancy:
            if current_start is None:
                current_start = day
        else:
            if current_start is not None:
                available_slots.append((current_start, day - 1))
                current_start = None
    
    if current_start is not None:
        available_slots.append((current_start, 27))
    
    # Sort available slots by duration (longest first)
    available_slots.sort(key=lambda x: -(x[1] - x[0] + 1))
    
    # Sort remaining cities by duration (longest first)
    remaining = sorted(remaining_cities.items(), key=lambda x: -x[1])
    
    # We'll try different orders for placing cities
    for attempt in range(100):  # Increased attempts
        temp_itinerary = fixed_segments.copy()
        temp_slots = available_slots.copy()
        temp_remaining = remaining.copy()
        success = True
        
        while temp_remaining and success:
            city, duration = temp_remaining.pop(0)
            placed = False
            
            # Try each available slot
            for i, (start, end) in enumerate(temp_slots):
                slot_duration = end - start + 1
                if slot_duration >= duration:
                    # Check flight connections with previous and next segments
                    prev_segment = None
                    next_segment = None
                    
                    # Find previous segment (if any)
                    for seg in temp_itinerary:
                        if seg['end'] < start:
                            if prev_segment is None or seg['end'] > prev_segment['end']:
                                prev_segment = seg
                    
                    # Find next segment (if any)
                    for seg in temp_itinerary:
                        if seg['start'] > end:
                            if next_segment is None or seg['start'] < next_segment['start']:
                                next_segment = seg
                    
                    # Check flight connections - more flexible approach
                    valid_placement = True
                    if prev_segment:
                        if city not in flights.get(prev_segment['place'], []):
                            valid_placement = False
                    if next_segment and valid_placement:
                        if city not in flights.get(next_segment['place'], []):
                            valid_placement = False
                    
                    if valid_placement:
                        # Place the city in this slot
                        new_seg = {'place': city, 'start': start, 'end': start + duration - 1}
                        temp_itinerary.append(new_seg)
                        
                        # Update available slots
                        if start + duration <= end:
                            temp_slots[i] = (start + duration, end)
                        else:
                            temp_slots.pop(i)
                        
                        # Re-sort slots by duration
                        temp_slots.sort(key=lambda x: -(x[1] - x[0] + 1))
                        placed = True
                        break
            
            if not placed:
                # Try to split the city's stay
                remaining_duration = duration
                temp_segments = []
                slots_used = []
                
                for i, (start, end) in enumerate(temp_slots):
                    if remaining_duration <= 0:
                        break
                    
                    slot_duration = end - start + 1
                    duration_to_use = min(slot_duration, remaining_duration)
                    
                    # Check flight connections
                    prev_segment = None
                    next_segment = None
                    
                    # Find previous segment (if any)
                    for seg in temp_itinerary + temp_segments:
                        if seg['end'] < start:
                            if prev_segment is None or seg['end'] > prev_segment['end']:
                                prev_segment = seg
                    
                    # Find next segment (if any)
                    for seg in temp_itinerary:
                        if seg['start'] > end:
                            if next_segment is None or seg['start'] < next_segment['start']:
                                next_segment = seg
                    
                    valid_placement = True
                    if prev_segment:
                        if city not in flights.get(prev_segment['place'], []):
                            valid_placement = False
                    if next_segment and valid_placement:
                        if city not in flights.get(next_segment['place'], []):
                            valid_placement = False
                    
                    if valid_placement:
                        new_seg = {'place': city, 'start': start, 'end': start + duration_to_use - 1}
                        temp_segments.append(new_seg)
                        remaining_duration -= duration_to_use
                        slots_used.append((i, start + duration_to_use))
                
                if remaining_duration == 0:
                    temp_itinerary.extend(temp_segments)
                    # Update available slots in reverse order
                    for i, new_start in sorted(slots_used, reverse=True):
                        start, end = temp_slots[i]
                        if new_start <= end:
                            temp_slots[i] = (new_start, end)
                        else:
                            temp_slots.pop(i)
                    # Re-sort slots by duration
                    temp_slots.sort(key=lambda x: -(x[1] - x[0] + 1))
                    placed = True
            
            if not placed:
                success = False
        
        if success:
            # Sort the itinerary by start day
            temp_itinerary.sort(key=lambda x: x['start'])
            
            # Verify all cities are visited
            visited_cities = set(seg['place'] for seg in temp_itinerary)
            if len(visited_cities) == len(cities):
                # Convert to the required output format
                itinerary_output = []
                for seg in temp_itinerary:
                    day_range = f"Day {seg['start']}-{seg['end']}"
                    itinerary_output.append({"day_range": day_range, "place": seg['place']})
                
                return {"itinerary": itinerary_output}
        
        # Try a different order for the remaining cities
        remaining = remaining[1:] + remaining[:1]
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))