from z3 import *
import itertools

def solve_scheduling():
    # Initialize solver with optimization
    opt = Optimize()

    # Define the friends and their constraints
    friends = [
        {"name": "Helen", "location": "North Beach", "available_start": "09:00", "available_end": "17:00", "min_duration": 15},
        {"name": "Kevin", "location": "Mission District", "available_start": "10:45", "available_end": "14:45", "min_duration": 45},
        {"name": "Amanda", "location": "Alamo Square", "available_start": "19:45", "available_end": "21:00", "min_duration": 60},
        {"name": "Betty", "location": "Financial District", "available_start": "19:00", "available_end": "21:45", "min_duration": 90}
    ]

    # Travel times dictionary
    travel_times = {
        "Pacific Heights": {"North Beach": 9, "Financial District": 13, "Alamo Square": 10, "Mission District": 15},
        "North Beach": {"Pacific Heights": 8, "Financial District": 8, "Alamo Square": 16, "Mission District": 18},
        "Financial District": {"Pacific Heights": 13, "North Beach": 7, "Alamo Square": 17, "Mission District": 17},
        "Alamo Square": {"Pacific Heights": 10, "North Beach": 15, "Financial District": 17, "Mission District": 10},
        "Mission District": {"Pacific Heights": 16, "North Beach": 17, "Financial District": 17, "Alamo Square": 11}
    }

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location and time
    current_location = "Pacific Heights"
    current_time = time_to_minutes("09:00")

    # Create meeting variables
    meetings = []
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')  # Whether this meeting is scheduled

        # Basic meeting constraints
        opt.add(Implies(scheduled, start >= available_start))
        opt.add(Implies(scheduled, end <= available_end))
        opt.add(Implies(scheduled, end == start + min_duration))
        opt.add(Implies(scheduled, start >= 0))
        opt.add(Implies(scheduled, end >= 0))

        meetings.append({
            "name": name,
            "location": friend["location"],
            "start": start,
            "end": end,
            "scheduled": scheduled,
            "min_duration": min_duration,
            "available_start": available_start,
            "available_end": available_end
        })

    # Create sequence variables
    sequence = [Int(f'seq_{i}') for i in range(len(meetings))]
    opt.add(Distinct(sequence))
    for i in range(len(sequence)):
        opt.add(sequence[i] >= 0)
        opt.add(sequence[i] < len(meetings))

    # Add ordering constraints
    prev_end = current_time
    prev_location = current_location
    for i in range(len(meetings)):
        # Get the meeting at this position in the sequence
        meeting_idx = sequence[i]
        meeting = meetings[meeting_idx]
        
        # Travel time from previous location
        travel_time = travel_times[prev_location][meeting["location"]]
        
        # Meeting must start after previous end plus travel time
        opt.add(Implies(meeting["scheduled"], meeting["start"] >= prev_end + travel_time))
        
        # Update previous end time and location
        new_prev_end = If(meeting["scheduled"], meeting["end"], prev_end)
        new_prev_location = If(meeting["scheduled"], meeting["location"], prev_location)
        prev_end = new_prev_end
        prev_location = new_prev_location

    # Maximize the number of scheduled meetings
    scheduled_count = Sum([If(m["scheduled"], 1, 0) for m in meetings])
    opt.maximize(scheduled_count)

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for meeting in meetings:
            if is_true(model[meeting["scheduled"]]):
                start_val = model[meeting["start"]].as_long()
                end_val = model[meeting["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)