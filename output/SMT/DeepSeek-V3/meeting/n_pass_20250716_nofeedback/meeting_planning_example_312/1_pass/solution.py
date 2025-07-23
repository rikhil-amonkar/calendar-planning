from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the districts and their travel times (in minutes)
    districts = {
        'Richmond': 0,
        'Sunset': 1,
        'Haight-Ashbury': 2,
        'Mission': 3,
        'Golden Gate Park': 4
    }
    
    travel_times = [
        [0, 11, 10, 20, 9],    # Richmond to others
        [12, 0, 15, 24, 11],    # Sunset to others
        [10, 15, 0, 11, 7],     # Haight-Ashbury to others
        [20, 24, 12, 0, 17],    # Mission to others
        [7, 10, 7, 17, 0]       # Golden Gate Park to others
    ]

    # Friends' data: name, district, available start, available end, min duration (minutes)
    friends = [
        ('Sarah', 'Sunset', 10*60 + 45, 19*60 + 0, 30),
        ('Richard', 'Haight-Ashbury', 11*60 + 45, 15*60 + 45, 90),
        ('Elizabeth', 'Mission', 11*60 + 0, 17*60 + 15, 120),
        ('Michelle', 'Golden Gate Park', 18*60 + 15, 20*60 + 45, 90)
    ]

    # Variables for each meeting: start and end times (in minutes since 9:00 AM)
    # Also, track the district of each meeting
    meeting_vars = []
    for i, (name, district, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars.append((name, district, start, end, min_dur, avail_start, avail_end))
    
    # Current time starts at 9:00 AM (0 minutes since start)
    current_time = 0
    current_district = districts['Richmond']
    
    # To model the sequence, we need to decide the order of meetings.
    # Since there are 4 friends, there are 4! = 24 possible orders.
    # We'll use a permutation approach to try all possible orders.
    # However, with Z3, we can model this with auxiliary variables.
    # But for simplicity, we'll predefine a reasonable order based on time windows.
    # Alternatively, we can use a more complex model with Z3's Array or other constructs.
    # Given the complexity, we'll proceed with a predefined order that seems logical.
    # The order is: Elizabeth (Mission), Richard (Haight-Ashbury), Sarah (Sunset), Michelle (Golden Gate Park).
    # This is based on their time windows and locations.

    # Alternatively, for a more dynamic approach, we can use Z3 to choose the order.
    # But that would require more complex modeling.
    # For now, we'll proceed with a fixed order.

    # Define the order: Elizabeth, Richard, Sarah, Michelle.
    order = [2, 1, 0, 3]  # Indices of friends in the order: Elizabeth, Richard, Sarah, Michelle

    # Now, model the meetings in this order.
    prev_end = 0  # start at 9:00 AM (0 minutes)
    prev_district = districts['Richmond']
    itinerary = []
    constraints = []

    for i in order:
        name, district, start, end, min_dur, avail_start, avail_end = meeting_vars[i]
        district_idx = districts[district]

        # Meeting must start after availability starts and end before availability ends
        constraints.append(start >= (avail_start - 9*60))
        constraints.append(end <= (avail_end - 9*60))
        constraints.append(end == start + min_dur)

        # Travel time from previous location
        travel_time = travel_times[prev_district][district_idx]
        constraints.append(start >= prev_end + travel_time)

        # Update previous end and district
        prev_end = end
        prev_district = district_idx

        # Add to itinerary
        itinerary.append({
            "name": name,
            "start": start,
            "end": end,
            "district": district
        })

    # Add all constraints to the solver
    for c in constraints:
        s.add(c)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        result = []
        for entry in itinerary:
            name = entry["name"]
            start_val = m.evaluate(entry["start"]).as_long()
            end_val = m.evaluate(entry["end"]).as_long()
            # Convert minutes since 9:00 AM to HH:MM
            start_hh = 9 + start_val // 60
            start_mm = start_val % 60
            end_hh = 9 + end_val // 60
            end_mm = end_val % 60
            start_time = f"{start_hh:02d}:{start_mm:02d}"
            end_time = f"{end_hh:02d}:{end_mm:02d}"
            result.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort the itinerary by start time
        result.sort(key=lambda x: x["start_time"])
        return {"itinerary": result}
    else:
        return {"error": "No feasible schedule found"}

# Run the solver and print the result
solution = solve_scheduling()
print(json.dumps(solution, indent=2))