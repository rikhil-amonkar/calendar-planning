from z3 import *
import datetime

# Define travel times between locations (in minutes)
travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# Friend availability information
friends = {
    "Richard": {
        "location": "Union Square",
        "available_start": datetime.time(8, 45),  # 8:45 AM
        "available_end": datetime.time(13, 0),    # 1:00 PM
        "min_duration": 120,                     # 2 hours
    },
    "Charles": {
        "location": "Presidio",
        "available_start": datetime.time(9, 45),  # 9:45 AM
        "available_end": datetime.time(13, 0),    # 1:00 PM
        "min_duration": 120,                     # 2 hours
    },
}

# Initialize solver
solver = Solver()

# Create variables for meeting times (in minutes since 9:00 AM)
meetings = {}
for name in friends:
    meetings[name] = {
        "start": Int(f"start_{name}"),
        "end": Int(f"end_{name}"),
    }

# Convert time to minutes since 9:00 AM
def time_to_minutes(t):
    base = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current = datetime.datetime.combine(datetime.date.today(), t)
    return int((current - base).total_seconds() / 60)

# Convert minutes back to time string
def minutes_to_time(m):
    base = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    delta = datetime.timedelta(minutes=int(m))
    current = base + delta
    return current.time().strftime("%H:%M")

# Add constraints for each friend's meeting
for name, info in friends.items():
    start = meetings[name]["start"]
    end = meetings[name]["end"]
    available_start = time_to_minutes(info["available_start"])
    available_end = time_to_minutes(info["available_end"])
    min_duration = info["min_duration"]

    # Meeting must start after friend becomes available (but not before 9:00 AM)
    solver.add(start >= max(0, available_start))
    
    # Meeting must end before friend becomes unavailable
    solver.add(end <= available_end)
    
    # Meeting duration must be at least min_duration
    solver.add(end - start >= min_duration)
    
    # Start must be before end
    solver.add(start < end)

# We start at Bayview at 9:00 AM (0 minutes)
current_location = "Bayview"
current_time = 0

# Try meeting Richard first
def try_richard_first():
    temp_solver = Solver()
    temp_solver.add(solver.assertions())
    
    # Travel to Union Square to meet Richard
    travel_time = travel_times[("Bayview", "Union Square")]
    temp_solver.add(meetings["Richard"]["start"] >= current_time + travel_time)
    
    # After meeting Richard, travel to Presidio to meet Charles
    travel_time = travel_times[("Union Square", "Presidio")]
    temp_solver.add(meetings["Charles"]["start"] >= meetings["Richard"]["end"] + travel_time)
    
    if temp_solver.check() == sat:
        return temp_solver.model()
    return None

# Try meeting Charles first
def try_charles_first():
    temp_solver = Solver()
    temp_solver.add(solver.assertions())
    
    # Travel to Presidio to meet Charles
    travel_time = travel_times[("Bayview", "Presidio")]
    temp_solver.add(meetings["Charles"]["start"] >= current_time + travel_time)
    
    # After meeting Charles, travel to Union Square to meet Richard
    travel_time = travel_times[("Presidio", "Union Square")]
    temp_solver.add(meetings["Richard"]["start"] >= meetings["Charles"]["end"] + travel_time)
    
    if temp_solver.check() == sat:
        return temp_solver.model()
    return None

# Try both orders
model = try_richard_first() or try_charles_first()

if model:
    itinerary = []
    for name in friends:
        start = model[meetings[name]["start"]].as_long()
        end = model[meetings[name]["end"]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })
    
    # Sort by start time
    itinerary.sort(key=lambda x: x["start_time"])
    
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No valid schedule found that meets all constraints")