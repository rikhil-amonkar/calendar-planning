import json

def main():
    travel_times = {
        ('PacificHeights', 'Presidio'): 11,
        ('PacificHeights', 'Marina'): 6,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'Presidio'): 10
    }
    
    constraints = {
        'Jason': (10 * 60, 16 * 60 + 15),    # 10:00 AM to 4:15 PM (600 to 975 minutes)
        'Kenneth': (15 * 60 + 30, 16 * 60 + 45)  # 3:30 PM to 4:45 PM (930 to 1005 minutes)
    }
    
    durations = {
        'Jason': 90,
        'Kenneth': 45
    }
    
    locations = {
        'Jason': 'Presidio',
        'Kenneth': 'Marina'
    }
    
    orders = [('Jason', 'Kenneth'), ('Kenneth', 'Jason')]
    base = 9 * 60  # 540 minutes (9:00 AM)
    departure_times = range(base, base + 21)  # 540 to 560 inclusive (9:00 AM to 9:20 AM)
    
    for order in orders:
        first_person, second_person = order
        first_loc = locations[first_person]
        second_loc = locations[second_person]
        
        for t in departure_times:
            # Travel to first location
            travel1 = travel_times[('PacificHeights', first_loc)]
            arrival1 = t + travel1
            
            # Calculate valid start times for first meeting
            s1_early = max(arrival1, constraints[first_person][0])
            s1_late = min(arrival1 + 20, constraints[first_person][1] - durations[first_person])
            
            if s1_early > s1_late:
                continue  # No valid start time for first meeting
                
            # Travel time between meetings
            travel2 = travel_times[(first_loc, second_loc)]
            total_time_first = durations[first_person] + travel2
            
            # Conditions for second meeting
            A2 = constraints[second_person][0]  # Available start time
            B2 = constraints[second_person][1] - durations[second_person]  # Latest start time
            
            # The second meeting must start between [A2-20, B2] after accounting for travel
            s1_min_candidate = A2 - 20 - total_time_first
            s1_max_candidate = B2 - total_time_first
            
            s1_min = max(s1_early, s1_min_candidate)
            s1_max = min(s1_late, s1_max_candidate)
            
            if s1_min <= s1_max:
                # Choose earliest valid s1
                s1 = s1_min
                # Calculate second meeting details
                arrival2 = s1 + total_time_first
                s2 = max(arrival2, A2)
                
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
                        "start": s2,
                        "end": s2 + durations[second_person]
                    }
                ]
                print(json.dumps({"itinerary": itinerary}))
                return
                
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()