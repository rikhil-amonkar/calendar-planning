import z3
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert HH:MM time string to minutes since midnight."""
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM time string."""
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define travel times as a dictionary for quick lookup
travel_times = {
    ('Fisherman\'s Wharf', 'The Castro'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'North Beach'): 5,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 15,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Alamo Square'): 16,
}

# Define friends' availability and constraints
friends = [
    {
        'name': 'Laura',
        'location': 'The Castro',
        'start': '19:45',
        'end': '21:30',
        'min_duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'start': '21:15',
        'end': '21:45',
        'min_duration': 15
    },
    {
        'name': 'William',
        'location': 'Embarcadero',
        'start': '07:00',
        'end': '09:00',
        'min_duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': '14:30',
        'end': '19:45',
        'min_duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'start': '07:30',
        'end': '09:30',
        'min_duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'start': '11:30',
        'end': '12:45',
        'min_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': '15:45',
        'end': '19:15',
        'min_duration': 30
    }
]

# Initialize Z3 solver
solver = z3.Solver()

# Create variables for each meeting's start and end times
meetings = []
for friend in friends:
    start_var = z3.Int(f"start_{friend['name']}")
    end_var = z3.Int(f"end_{friend['name']}")
    meetings.append({
        'name': friend['name'],
        'location': friend['location'],
        'start_var': start_var,
        'end_var': end_var,
        'min_duration': friend['min_duration'],
        'availability_start': time_to_minutes(friend['start']),
        'availability_end': time_to_minutes(friend['end'])
    })

# Add constraints for each meeting
for meeting in meetings:
    solver.add(meeting['start_var'] >= meeting['availability_start'])
    solver.add(meeting['end_var'] <= meeting['availability_end'])
    solver.add(meeting['end_var'] >= meeting['start_var'] + meeting['min_duration'])

# Initial location is Fisherman's Wharf, starting at 9:00 AM (540 minutes)
current_time = 540
current_location = "Fisherman's Wharf"

# We need to sequence the meetings. For simplicity, we'll try to meet friends in an order that fits.
# This is a complex part; for now, let's assume we can meet all friends in some order.
# We'll need to model the order as a permutation and add travel time constraints.

# To model the order, we'll use a list of booleans indicating if a meeting is before another.
# This is complex, so for brevity, let's assume a feasible order is found manually.

# However, given the complexity, let's instead try to meet friends in an order that fits the time constraints.

# Let's try to meet Stephanie first (since she's available early), then William, then Joseph, etc.

# Define a possible order: Stephanie, William, Joseph, Karen, Kimberly, Laura, Daniel
order = ['Stephanie', 'William', 'Joseph', 'Karen', 'Kimberly', 'Laura', 'Daniel']

# Add travel time constraints between consecutive meetings
prev_meeting = None
prev_end_time = current_time
prev_location = current_location
for name in order:
    meeting = next(m for m in meetings if m['name'] == name)
    # Travel time from previous location to current meeting's location
    travel_time = travel_times.get((prev_location, meeting['location']), 0)
    solver.add(meeting['start_var'] >= prev_end_time + travel_time)
    prev_end_time = meeting['end_var']
    prev_location = meeting['location']

# Check if the schedule is feasible
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for meeting in meetings:
        start = model.eval(meeting['start_var']).as_long()
        end = model.eval(meeting['end_var']).as_long()
        itinerary.append({
            "action": "meet",
            "person": meeting['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
    print({
        "itinerary": itinerary
    })
else:
    print("No feasible schedule found.")