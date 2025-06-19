import json

def main():
    # Travel times in minutes
    travel_times = {
        ('PacificHeights', 'Presidio'): 11,
        ('PacificHeights', 'Marina'): 6,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'Presidio'): 10
    }
    
    # Constraints: (available_start, available_end) in minutes since midnight
    constraints = {
        'Jason': (10 * 60, 16 * 60 + 15),    # 10:00 AM to 4:15 PM
        'Kenneth': (15 * 60 + 30, 16 * 60 + 45)  # 3:30 PM to 4:45 PM
    }
    
    # Meeting durations in minutes
    durations = {
        'Jason': 90,
        'Kenneth': 45
    }
    
    # Meeting locations
    locations = {
        'Jason': 'Presidio',
        'Kenneth': 'Marina'
    }
    
    # Possible meeting orders
    orders = [('Jason', 'Kenneth'), ('Kenneth', 'Jason')]
    
    # Departure times from Pacific Heights (9:00 AM to 9:20 AM)
    base = 9 * 60  # 540 minutes (9:00 AM)
    departure_times = range(base, base + 21)  # 540 to 560 inclusive
    
    for order in orders:
        for t in departure_times:
            # First meeting details
            first_person = order[0]
            first_loc = locations[first_person]
            travel1 = travel_times[('PacificHeights', first_loc)]
            arrival1 = t + travel1
            
            # Calculate valid start times for first meeting
            s1_early = max(arrival1, constraints[first_person][0])
            s1_late = min(arrival1 + 20, constraints[first_person][1] - durations[first_person])
            
            if s1_early > s1_late:
                continue  # No valid start time for first meeting
                
            # Try both earliest and latest start times
            for s1 in [s1_early, s1_late]:
                # Time after first meeting
                leave1 = s1 + durations[first_person]
                
                # Second meeting details
                second_person = order[1]
                second_loc = locations[second_person]
                travel2_key = (first_loc, second_loc)
                travel2 = travel_times[travel2_key]
                arrival2 = leave1 + travel2
                
                # Calculate valid start times for second meeting
                s2_early = max(arrival2, constraints[second_person][0])
                s2_late = min(arrival2 + 20, constraints[second_person][1] - durations[second_person])
                
                if s2_early <= s2_late:
                    # Found valid itinerary
                    itinerary = [
                        {
                            "location": first_loc,
                            "name": first_person,
                            "start": s1,
                            "end": s1 + durations[first_person]
                        },
                        {
                            "location": second_loc,
                            "name": second_person,
                            "start": s2_early,
                            "end": s2_early + durations[second_person]
                        }
                    ]
                    print(json.dumps({"itinerary": itinerary}))
                    return
    
    # No feasible itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()