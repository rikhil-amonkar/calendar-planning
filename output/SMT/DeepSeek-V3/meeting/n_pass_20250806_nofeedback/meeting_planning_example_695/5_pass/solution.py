from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Friend data with adjusted priorities
    friends = [
        {"name": "Carol", "location": "Union Square", "start": "18:00", "end": "20:15", "min_duration": 120, "priority": 1},
        {"name": "Patricia", "location": "Chinatown", "start": "20:00", "end": "21:30", "min_duration": 75, "priority": 2},
        {"name": "Jeffrey", "location": "Pacific Heights", "start": "20:00", "end": "20:45", "min_duration": 45, "priority": 3},
        {"name": "Paul", "location": "Nob Hill", "start": "16:15", "end": "21:15", "min_duration": 60, "priority": 4},
        {"name": "Karen", "location": "The Castro", "start": "17:00", "end": "19:00", "min_duration": 45, "priority": 5},
        {"name": "Matthew", "location": "Russian Hill", "start": "15:45", "end": "21:45", "min_duration": 75, "priority": 6},
        {"name": "Nancy", "location": "Presidio", "start": "11:45", "end": "22:00", "min_duration": 30, "priority": 7}
    ]

    # Sort friends by priority (tighter windows first)
    friends.sort(key=lambda x: x["priority"])

    # Travel times matrix
    locations = ["Bayview", "Nob Hill", "Union Square", "Chinatown", 
                "The Castro", "Presidio", "Pacific Heights", "Russian Hill"]
    
    travel_matrix = [
        [0, 20, 17, 18, 20, 31, 23, 23],
        [19, 0, 7, 6, 17, 17, 8, 5],
        [15, 9, 0, 7, 19, 24, 15, 13],
        [22, 8, 7, 0, 22, 19, 10, 7],
        [19, 16, 19, 20, 0, 20, 16, 18],
        [31, 18, 22, 21, 21, 0, 11, 14],
        [22, 8, 12, 11, 16, 11, 0, 7],
        [23, 5, 11, 9, 21, 14, 7, 0]
    ]

    def get_travel_time(from_loc, to_loc):
        from_idx = locations.index(from_loc)
        to_idx = locations.index(to_loc)
        return travel_matrix[from_idx][to_idx]

    # Time conversion helpers
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create meeting variables
    meetings = []
    for friend in friends:
        name = friend["name"]
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        min_duration = friend["min_duration"]
        window_start = time_to_minutes(friend["start"])
        window_end = time_to_minutes(friend["end"])
        
        s.add(start >= window_start)
        s.add(end <= window_end)
        s.add(end - start >= min_duration)
        
        meetings.append({
            "name": name,
            "location": friend["location"],
            "start": start,
            "end": end,
            "min_duration": min_duration
        })

    # Current state
    current_loc = "Bayview"
    current_time = 540  # 9:00 AM

    # Try to schedule meetings in priority order
    scheduled = []
    for i, meeting in enumerate(meetings):
        # Add travel time constraint
        travel_time = get_travel_time(current_loc, meeting["location"])
        s.add(meeting["start"] >= current_time + travel_time)
        
        # Add non-overlapping constraints with previous meetings
        for prev in scheduled:
            s.add(Or(
                meeting["end"] <= prev["start"] - get_travel_time(meeting["location"], prev["location"]),
                prev["end"] <= meeting["start"] - get_travel_time(prev["location"], meeting["location"])
            ))
        
        scheduled.append(meeting)
        current_time = meeting["end"]
        current_loc = meeting["location"]

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        for meeting in meetings:
            start_val = model.eval(meeting["start"]).as_long()
            end_val = model.eval(meeting["end"]).as_long()
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

result = solve_scheduling()
print(json.dumps(result, indent=2))