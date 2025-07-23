import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Brussels': {'duration': 5, 'constraints': [('workshop', 7, 11)]},
        'Rome': {'duration': 2, 'constraints': []},
        'Dubrovnik': {'duration': 3, 'constraints': []},
        'Geneva': {'duration': 5, 'constraints': []},
        'Budapest': {'duration': 2, 'constraints': [('meet_friend', 16, 17)]},
        'Riga': {'duration': 4, 'constraints': [('tour_with_friends', 4, 7)]},
        'Valencia': {'duration': 2, 'constraints': []}
    }

    direct_flights = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Budapest': ['Geneva', 'Rome', 'Brussels'],
        'Riga': ['Rome', 'Brussels'],
        'Valencia': ['Brussels', 'Rome', 'Geneva']
    }

    # We'll try different approaches to place the constrained cities
    # First, let's place the cities with the tightest constraints
    
    # Riga must cover days 4-7 (4 days)
    # So possible start days: 1 (ends day 4), 2 (ends day 5), 3 (ends day 6), 4 (ends day 7)
    possible_riga = [1, 2, 3, 4]
    
    # Brussels must cover days 7-11 (5 days)
    # Possible start days: 3 (ends day 7), 4 (ends day 8), 5 (ends day 9), 6 (ends day 10), 7 (ends day 11)
    possible_brussels = [3, 4, 5, 6, 7]
    
    # Budapest must cover days 16-17 (2 days)
    # Must start on day 16 (ends day 17)
    possible_budapest = [16]
    
    # Try all combinations of these constrained cities
    for riga_start in possible_riga:
        riga_end = riga_start + cities['Riga']['duration'] - 1
        if riga_end < 4 or riga_start > 7:  # Must cover days 4-7
            continue
            
        for brussels_start in possible_brussels:
            brussels_end = brussels_start + cities['Brussels']['duration'] - 1
            if brussels_end < 7 or brussels_start > 11:  # Must cover days 7-11
                continue
                
            # Check if Riga and Brussels overlap or conflict
            if (brussels_start <= riga_end and riga_start <= brussels_end):
                continue  # They overlap, which is impossible
                
            for budapest_start in possible_budapest:
                budapest_end = budapest_start + cities['Budapest']['duration'] - 1
                if budapest_end < 16 or budapest_start > 17:  # Must cover days 16-17
                    continue
                    
                # Now place the remaining cities (Rome, Dubrovnik, Geneva, Valencia)
                remaining_cities = ['Rome', 'Dubrovnik', 'Geneva', 'Valencia']
                
                # Try all permutations of remaining cities
                for perm in permutations(remaining_cities):
                    # Build the full itinerary with timing
                    full_itinerary = []
                    day_assignments = {}
                    
                    # Assign the constrained cities first
                    day_assignments['Riga'] = (riga_start, riga_end)
                    day_assignments['Brussels'] = (brussels_start, brussels_end)
                    day_assignments['Budapest'] = (budapest_start, budapest_end)
                    
                    # Assign remaining cities to available slots
                    available_slots = []
                    current_day = 1
                    
                    # Create timeline of occupied days
                    occupied = set()
                    for city in ['Riga', 'Brussels', 'Budapest']:
                        start, end = day_assignments[city]
                        occupied.update(range(start, end + 1))
                    
                    # Find available slots between constrained cities
                    all_days = sorted(occupied.union({1, 17}))
                    for i in range(len(all_days) - 1):
                        gap_start = all_days[i] + 1
                        gap_end = all_days[i+1] - 1
                        if gap_start <= gap_end:
                            available_slots.append((gap_start, gap_end))
                    
                    # Also check before first constrained city and after last
                    first_constrained_day = min(occupied)
                    if first_constrained_day > 1:
                        available_slots.insert(0, (1, first_constrained_day - 1))
                    
                    last_constrained_day = max(occupied)
                    if last_constrained_day < 17:
                        available_slots.append((last_constrained_day + 1, 17))
                    
                    # Try to fit remaining cities into available slots
                    remaining_cities_order = list(perm)
                    remaining_durations = [cities[city]['duration'] for city in remaining_cities_order]
                    
                    # Try to fit cities into slots
                    city_assignments = {}
                    slot_index = 0
                    city_index = 0
                    valid = True
                    
                    while city_index < len(remaining_cities_order) and slot_index < len(available_slots):
                        city = remaining_cities_order[city_index]
                        duration = cities[city]['duration']
                        slot_start, slot_end = available_slots[slot_index]
                        
                        if slot_end - slot_start + 1 >= duration:
                            # Place city here
                            city_assignments[city] = (slot_start, slot_start + duration - 1)
                            # Update the slot
                            if slot_start + duration <= slot_end:
                                available_slots[slot_index] = (slot_start + duration, slot_end)
                            else:
                                slot_index += 1
                            city_index += 1
                        else:
                            slot_index += 1
                    
                    if city_index < len(remaining_cities_order):
                        valid = False
                    
                    if not valid:
                        continue
                    
                    # Combine all city assignments
                    all_city_assignments = {**day_assignments, **city_assignments}
                    
                    # Verify flight connections
                    city_order = sorted(all_city_assignments.keys(), key=lambda x: all_city_assignments[x][0])
                    valid_flights = True
                    
                    for i in range(len(city_order) - 1):
                        current_city = city_order[i]
                        next_city = city_order[i+1]
                        if next_city not in direct_flights[current_city]:
                            valid_flights = False
                            break
                    
                    if not valid_flights:
                        continue
                    
                    # Build the itinerary
                    itinerary = []
                    for city in city_order:
                        start, end = all_city_assignments[city]
                        day_range = f"Day {start}-{end}"
                        itinerary.append({'day_range': day_range, 'place': city})
                    
                    # Verify total days is exactly 17
                    last_day = max([end for start, end in all_city_assignments.values()])
                    if last_day != 17:
                        continue
                    
                    return {'itinerary': itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))