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
    
    # Remaining cities and their durations
    remaining = list(remaining_cities.items())
    
    # We'll try to place cities in the available slots
    itinerary = fixed_segments.copy()
    
    # Helper function to check flight connections
    def has_flight(city1, city2):
        return city1 in flights.get(city2, []) or city2 in flights.get(city1, [])
    
    # Try to place remaining cities
    for city, duration in remaining:
        placed = False
        
        # Try each available slot
        for i, (start, end) in enumerate(available_slots):
            slot_duration = end - start + 1
            if slot_duration >= duration:
                # Check if we can place here considering flight connections
                prev_segment = None
                next_segment = None
                
                # Find previous segment (if any)
                for seg in itinerary:
                    if seg['end'] < start:
                        if prev_segment is None or seg['end'] > prev_segment['end']:
                            prev_segment = seg
                
                # Find next segment (if any)
                for seg in itinerary:
                    if seg['start'] > end:
                        if next_segment is None or seg['start'] < next_segment['start']:
                            next_segment = seg
                
                # Check flight connections
                valid_placement = True
                if prev_segment:
                    if not has_flight(prev_segment['place'], city):
                        valid_placement = False
                if next_segment and valid_placement:
                    if not has_flight(city, next_segment['place']):
                        valid_placement = False
                
                if valid_placement:
                    # Place the city in this slot
                    new_seg = {'place': city, 'start': start, 'end': start + duration - 1}
                    itinerary.append(new_seg)
                    
                    # Update available slots
                    if start + duration <= end:
                        available_slots[i] = (start + duration, end)
                    else:
                        available_slots.pop(i)
                    
                    placed = True
                    break
        
        if not placed:
            # Try to split the city's stay across multiple slots
            remaining_duration = duration
            temp_segments = []
            
            for i, (start, end) in enumerate(available_slots):
                if remaining_duration <= 0:
                    break
                
                slot_duration = end - start + 1
                duration_to_use = min(slot_duration, remaining_duration)
                
                # Check flight connections
                prev_segment = None
                next_segment = None
                
                # Find previous segment (if any)
                for seg in itinerary + temp_segments:
                    if seg['end'] < start:
                        if prev_segment is None or seg['end'] > prev_segment['end']:
                            prev_segment = seg
                
                # Find next segment (if any)
                for seg in itinerary:
                    if seg['start'] > end:
                        if next_segment is None or seg['start'] < next_segment['start']:
                            next_segment = seg
                
                valid_placement = True
                if prev_segment:
                    if not has_flight(prev_segment['place'], city):
                        valid_placement = False
                if next_segment and valid_placement:
                    if not has_flight(city, next_segment['place']):
                        valid_placement = False
                
                if valid_placement:
                    new_seg = {'place': city, 'start': start, 'end': start + duration_to_use - 1}
                    temp_segments.append(new_seg)
                    remaining_duration -= duration_to_use
                    
                    # Update available slots
                    if start + duration_to_use <= end:
                        available_slots[i] = (start + duration_to_use, end)
                    else:
                        available_slots.pop(i)
            
            if remaining_duration == 0:
                itinerary.extend(temp_segments)
                placed = True
        
        if not placed:
            return {"itinerary": []}
    
    # Sort the itinerary by start day
    itinerary.sort(key=lambda x: x['start'])
    
    # Convert to the required output format
    itinerary_output = []
    for seg in itinerary:
        day_range = f"Day {seg['start']}-{seg['end']}"
        itinerary_output.append({"day_range": day_range, "place": seg['place']})
    
    return {"itinerary": itinerary_output}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))