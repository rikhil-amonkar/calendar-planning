from z3 import *
import datetime

# Define the travel times between locations
travel_times = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# Define the constraints for each friend
friends = {
    "Richard": {
        "location": "Union Square",
        "available_start": datetime.time(8, 45),
        "available_end": datetime.time(13, 0),
        "min_duration": 120,
    },
    "Charles": {
        "location": "Presidio",
        "available_start": datetime.time(9, 45),
        "available_end": datetime.time(13, 0),
        "min_duration": 120,
    },
}

# Initialize the solver
solver = Solver()

# Create variables for the start and end times of each meeting
meetings = {}
for name in friends:
    meetings[name] = {
        "start": Int(f"start_{name}"),
        "end": Int(f"end_{name}"),
    }

# Convert time to minutes since 9:00 AM (arrival time)
def time_to_minutes(time):
    arrival = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current = datetime.datetime.combine(datetime.date.today(), time)
    delta = current - arrival
    return int(delta.total_seconds() / 60)

# Convert minutes back to time string
def minutes_to_time(minutes):
    arrival = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    delta = datetime.timedelta(minutes=int(minutes))
    current = arrival + delta
    return current.time().strftime("%H:%M")

# Add constraints for each meeting
for name, info in friends.items():
    start = meetings[name]["start"]
    end = meetings[name]["end"]
    available_start = time_to_minutes(info["available_start"])
    available_end = time_to_minutes(info["available_end"])
    min_duration = info["min_duration"]

    # Meeting must start and end within the friend's availability
    solver.add(start >= available_start)
    solver.add(end <= available_end)
    # Meeting duration must be at least min_duration
    solver.add(end - start >= min_duration)
    # Start time must be before end time
    solver.add(start < end)

# Add constraints for travel times
# We start at Bayview at 0 minutes (9:00 AM)
current_location = "Bayview"
current_time = 0

# We need to decide the order of meetings: Richard first or Charles first
order = ["Richard", "Charles"]
for i in range(len(order)):
    name = order[i]
    location = friends[name]["location"]
    travel_time = travel_times[(current_location, location)]
    
    # The meeting can only start after arriving at the location
    solver.add(meetings[name]["start"] >= current_time + travel_time)
    
    # After the meeting, update current location and time
    current_location = location
    current_time = meetings[name]["end"]
    
    # If there's another meeting, add travel time to the next location
    if i < len(order) - 1:
        next_name = order[i + 1]
        next_location = friends[next_name]["location"]
        travel_time_next = travel_times[(current_location, next_location)]
        solver.add(meetings[next_name]["start"] >= current_time + travel_time_next)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for name in order:
        start = model[meetings[name]["start"]].as_long()
        end = model[meetings[name]["end"]].as_long()
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No solution found")