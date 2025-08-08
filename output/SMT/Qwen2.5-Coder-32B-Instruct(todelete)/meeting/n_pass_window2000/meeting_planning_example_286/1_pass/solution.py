from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

# Define the available times for each person
available_times = {
    'Rebecca': (time_in_minutes(11, 30), time_in_minutes(20, 15)),
    'Karen': (time_in_minutes(12, 45), time_in_minutes(15, 0)),
    'Carol': (time_in_minutes(10, 15), time_in_minutes(11, 45)),
}

# Define the minimum meeting times
min_meeting_times = {
    'Rebecca': 120,
    'Karen': 120,
    'Carol': 30,
}

# Define the solver
solver = Solver()

# Define the start and end times for each meeting
meeting_start_times = {person: Int(f'start_{person}') for person in available_times}
meeting_end_times = {person: Int(f'end_{person}') for person in available_times}

# Add constraints for each meeting
for person, (start, end) in available_times.items():
    solver.add(meeting_start_times[person] >= start)
    solver.add(meeting_end_times[person] <= end)
    solver.add(meeting_end_times[person] - meeting_start_times[person] >= min_meeting_times[person])

# Add constraints for travel times
locations = ['Union Square', 'Mission District', 'Bayview', 'Sunset District']
current_location = 'Union Square'
current_time = 0

# Define the order of meetings
order = ['Carol', 'Rebecca', 'Karen']  # Initial guess, will be optimized

# Add constraints for travel and meeting order
for i in range(len(order) - 1):
    person1 = order[i]
    person2 = order[i + 1]
    travel_time = travel_times[(current_location, available_times[person1][0])]
    solver.add(meeting_start_times[person1] >= current_time + travel_time)
    current_time = meeting_end_times[person1]
    travel_time = travel_times[(available_times[person1][1], available_times[person2][0])]
    solver.add(meeting_start_times[person2] >= current_time + travel_time)
    current_location = available_times[person2][0]

# Add constraint for the last meeting
person = order[-1]
travel_time = travel_times[(current_location, available_times[person][0])]
solver.add(meeting_start_times[person] >= current_time + travel_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in order:
        start_time = model[meeting_start_times[person]].as_long()
        end_time = model[meeting_end_times[person]].as_long()
        start_hour = start_time // 60 + 9
        start_minute = start_time % 60
        end_hour = end_time // 60 + 9
        end_minute = end_time % 60
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start_hour:02}:{start_minute:02}",
            "end_time": f"{end_hour:02}:{end_minute:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")