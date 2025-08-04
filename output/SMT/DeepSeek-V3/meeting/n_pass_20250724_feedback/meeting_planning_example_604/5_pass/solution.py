import z3
from itertools import combinations

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define travel times (same as before)
travel_times = {
    # ... (same travel times dictionary as previous solutions)
}

friends = [
    # ... (same friends data as previous solutions)
]

# Initialize solver
solver = z3.Solver()

# Create meeting variables
meetings = []
for friend in friends:
    start = z3.Int(f"start_{friend['name']}")
    end = z3.Int(f"end_{friend['name']}")
    meetings.append({
        'name': friend['name'],
        'location': friend['location'],
        'start': start,
        'end': end,
        'min_duration': friend['min_duration'],
        'availability_start': time_to_minutes(friend['start']),
        'availability_end': time_to_minutes(friend['end'])
    })

# Add basic constraints
for m in meetings:
    solver.add(m['start'] >= m['availability_start'])
    solver.add(m['end'] <= m['availability_end'])
    solver.add(m['end'] >= m['start'] + m['min_duration'])

# Add ordering constraints to prevent overlaps
for m1, m2 in combinations(meetings, 2):
    # Either m1 is before m2 or vice versa
    solver.add(z3.Or(
        m1['end'] + travel_times.get((m1['location'], m2['location']), 0) <= m2['start'],
        m2['end'] + travel_times.get((m2['location'], m1['location']), 0) <= m1['start']
    ))

# Starting point
current_time = 540  # 9:00 AM
current_location = "Fisherman's Wharf"

# Add constraints for first meeting
first_meeting = meetings[0]
solver.add(first_meeting['start'] >= current_time + travel_times.get((current_location, first_meeting['location']), 0))

# Try to solve
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for m in meetings:
        start = model.eval(m['start']).as_long()
        end = model.eval(m['end']).as_long()
        itinerary.append({
            "action": "meet",
            "person": m['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    # Sort by start time
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
    print({
        "itinerary": itinerary
    })
else:
    print("No feasible schedule found.")