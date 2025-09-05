from z3 import *
import json

def minutes_to_time_str(m):
    # Convert minutes from midnight to H:MM format (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friend meeting constraints and info
    friends = [
        {"name": "Jason", "location": "Richmond District", "avail_start": 13*60, "avail_end": 20*60 + 45, "min_duration": 90},
        {"name": "Melissa", "location": "North Beach", "avail_start": 18*60 + 45, "avail_end": 20*60 + 15, "min_duration": 45},
        {"name": "Brian", "location": "Financial District", "avail_start": 9*60 + 45, "avail_end": 21*60 + 45, "min_duration": 15},
        {"name": "Elizabeth", "location": "Golden Gate Park", "avail_start": 8*60 + 45, "avail_end": 21*60 + 30, "min_duration": 105},
        {"name": "Laura", "location": "Union Square", "avail_start": 14*60 + 15, "avail_end": 19*60 + 30, "min_duration": 75}
    ]
    n = len(friends)
    
    # Define travel distances in minutes between locations
    travel = {
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Union Square"): 21,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Union Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22
    }
    
    # Create an Optimize instance
    opt = Optimize()
    
    # Decision variables: start time, meeting duration, and order of meetings; also compute end time.
    starts = [Int(f"start_{i}") for i in range(n)]
    durations = [Int(f"duration_{i}") for i in range(n)]
    ends = [Int(f"end_{i}") for i in range(n)]
    orders = [Int(f"order_{i}") for i in range(n)]
    
    # Final time variable representing the finish time of the last meeting.
    final_time = Int("final_time")
    
    # Add constraints for each friend's meeting
    for i, friend in enumerate(friends):
        # Meeting must start after the friend's available start time.
        opt.add(starts[i] >= friend["avail_start"])
        # Meeting must finish by the friend's available end time.
        opt.add(starts[i] + durations[i] <= friend["avail_end"])
        # Enforce the minimum meeting duration.
        opt.add(durations[i] >= friend["min_duration"])
        # Define the meeting's end time.
        opt.add(ends[i] == starts[i] + durations[i])
        # Order number must be between 0 and n-1.
        opt.add(orders[i] >= 0, orders[i] < n)
    
    # All meetings must have a unique order.
    opt.add(Distinct(orders))
    
    # Add travel constraints between meetings:
    # If meeting i is scheduled before meeting j then meeting i's end time plus travel time must be <= meeting j's start time.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_time = travel[(friends[i]["location"], friends[j]["location"])]
                opt.add(If(orders[i] < orders[j], ends[i] + travel_time <= starts[j], True))
    
    # Constraint for the first meeting: Departing from Presidio at 9:00 (540 minutes).
    for i in range(n):
        travel_from_presidio = travel[("Presidio", friends[i]["location"])]
        opt.add(If(orders[i] == 0, 540 + travel_from_presidio <= starts[i], True))
    
    # Define final_time as at least every meeting's end time.
    for i in range(n):
        opt.add(final_time >= ends[i])
    opt.add(final_time >= 540)
    
    # Objective: Minimize the final_time to obtain a compact schedule.
    opt.minimize(final_time)
    
    # Check and extract the solution.
    if opt.check() == sat:
        model = opt.model()
        # Build the itinerary sorted by the meeting order.
        itinerary = []
        meeting_order = sorted(range(n), key=lambda i: model[orders[i]].as_long())
        for i in meeting_order:
            event = {
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time_str(model[starts[i]].as_long()),
                "end_time": minutes_to_time_str(model[ends[i]].as_long())
            }
            itinerary.append(event)
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()