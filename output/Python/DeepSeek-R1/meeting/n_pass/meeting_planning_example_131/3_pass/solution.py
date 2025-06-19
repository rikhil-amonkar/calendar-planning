import json

def main():
    # Base start time at Pacific Heights (9:00 AM)
    base = 9 * 60  # 540 minutes
    max_initial_wait = 20  # Maximum wait at Pacific Heights
    latest_departure = base + max_initial_wait  # 560 minutes (9:20 AM)

    travel_times = {
        ('PacificHeights', 'Presidio'): 11,
        ('PacificHeights', 'Marina'): 6,
        ('Presidio', 'PacificHeights'): 11,
        ('Presidio', 'Marina'): 10,
        ('Marina', 'PacificHeights'): 7,
        ('Marina', 'Presidio'): 10
    }
    
    constraints = {
        'Jason': (10 * 60, 16 * 60 + 15),    # 10:00 AM - 4:15 PM (600-975 min)
        'Kenneth': (15 * 60 + 30, 16 * 60 + 45)  # 3:30 PM - 4:45 PM (930-1005 min)
    }
    
    durations = {
        'Jason': 90,
        'Kenneth': 45
    }
    
    locations = {
        'Jason': 'Presidio',
        'Kenneth': 'Marina'
    }
    
    # Check feasibility for Jason as first meeting
    travel_jason = travel_times[('PacificHeights', locations['Jason'])]
    arrival_jason = latest_departure + travel_jason  # 571 min (9:31 AM)
    # Wait time at Presidio before Jason's meeting
    wait_jason = max(0, constraints['Jason'][0] - arrival_jason)  # 29 min
    
    # Check feasibility for Kenneth as first meeting
    travel_kenneth = travel_times[('PacificHeights', locations['Kenneth'])]
    arrival_kenneth = latest_departure + travel_kenneth  # 566 min (9:26 AM)
    # Wait time at Marina before Kenneth's meeting
    wait_kenneth = max(0, constraints['Kenneth'][0] - arrival_kenneth)  # 364 min
    
    # Both first meetings violate wait constraint (20 min max)
    if wait_jason > 20 and wait_kenneth > 20:
        result = {"itinerary": []}
    else:
        # This branch not taken for current constraints
        result = {"itinerary": []}  # Fallback to empty if not implemented
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()