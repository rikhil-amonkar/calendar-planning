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

# Define the locations and initial location
locations = ['Union Square', 'Mission District', 'Bayview', 'Sunset District']
current_location = 'Union Square'
current_time = 0

# Define the order of meetings
order = ['Carol', 'Rebecca', 'Karen']  # Initial guess, will be optimized

# Add constraints for travel and meeting order
for i in range(len(order)):
    person = order[i]
    if i == 0:
        # First meeting, start from Union Square
        travel_time = travel_times[(current_location, 'Mission District' if person == 'Rebecca' else 'Bayview' if person == 'Karen' else 'Sunset District')]
        solver.add(meeting_start_times[person] >= current_time + travel_time)
    else:
        # Subsequent meetings, travel from previous meeting location
        prev_person = order[i - 1]
        prev_location = 'Mission District' if prev_person == 'Rebecca' else 'Bayview' if prev_person == 'Karen' else 'Sunset District'
        current_location = 'Mission District' if person == 'Rebecca' else 'Bayview' if person == 'Karen' else 'Sunset District'
        travel_time = travel_times[(prev_location, current_location)]
        solver.add(meeting_start_times[person] >= meeting_end_times[prev_person] + travel_time)

# Add constraint for the last meeting to end before the day is over (21:00PM)
last_person = order[-1]
solver.add(meeting_end_times[last_person] <= time_in_minutes(21, 0))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in order:
        start_time = model[meeting_start_times[person]].as_long()
        end_time = model[meeting_end_times[person]].as_long()
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{(start_time // 60 + 9):02}:{start_time % 60:02}",
            "end_time": f"{(end_time // 60 + 9):02}:{end_time % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")

# If no solution is found, try a different order
if solver.check() != sat:
    # Try a different order: Carol, Karen, Rebecca
    order = ['Carol', 'Karen', 'Rebecca']
    solver.reset()
    for person, (start, end) in available_times.items():
        solver.add(meeting_start_times[person] >= start)
        solver.add(meeting_end_times[person] <= end)
        solver.add(meeting_end_times[person] - meeting_start_times[person] >= min_meeting_times[person])
    
    for i in range(len(order)):
        person = order[i]
        if i == 0:
            travel_time = travel_times[(current_location, 'Mission District' if person == 'Rebecca' else 'Bayview' if person == 'Karen' else 'Sunset District')]
            solver.add(meeting_start_times[person] >= current_time + travel_time)
        else:
            prev_person = order[i - 1]
            prev_location = 'Mission District' if prev_person == 'Rebecca' else 'Bayview' if prev_person == 'Karen' else 'Sunset District'
            current_location = 'Mission District' if person == 'Rebecca' else 'Bayview' if person == 'Karen' else 'Sunset District'
            travel_time = travel_times[(prev_location, current_location)]
            solver.add(meeting_start_times[person] >= meeting_end_times[prev_person] + travel_time)
    
    solver.add(meeting_end_times[last_person] <= time_in_minutes(21, 0))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person in order:
            start_time = model[meeting_start_times[person]].as_long()
            end_time = model[meeting_end_times[person]].as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{(start_time // 60 + 9):02}:{start_time % 60:02}",
                "end_time": f"{(end_time // 60 + 9):02}:{end_time % 60:02}"
            })
        print({"itinerary": itinerary})
    else:
        print("No solution found")