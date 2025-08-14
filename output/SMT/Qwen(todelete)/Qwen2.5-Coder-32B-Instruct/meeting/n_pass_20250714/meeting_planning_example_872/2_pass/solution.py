from z3 import *

# Define the time slots in minutes from 9:00 AM (0) to 11:15 PM (735)
time_slots = range(736)

# Define the meeting times as integer variables
karen_meeting_start = Int('karen_meeting_start')
jessica_meeting_start = Int('jessica_meeting_start')
brian_meeting_start = Int('brian_meeting_start')
kenneth_meeting_start = Int('kenneth_meeting_start')
jason_meeting_start = Int('jason_meeting_start')
stephanie_meeting_start = Int('stephanie_meeting_start')
kimberly_meeting_start = Int('kimberly_meeting_start')
steven_meeting_start = Int('steven_meeting_start')
mark_meeting_start = Int('mark_meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for each friend
# Karen: 9:00 PM to 9:45 PM, 45 minutes
solver.add(karen_meeting_start >= 540)  # 9:00 PM in minutes
solver.add(karen_meeting_start + 45 <= 585)  # 9:45 PM in minutes

# Jessica: 1:45 PM to 9:00 PM, 90 minutes
solver.add(jessica_meeting_start >= 345)  # 1:45 PM in minutes
solver.add(jessica_meeting_start + 90 <= 540)  # 9:00 PM in minutes

# Brian: 3:30 PM to 9:45 PM, 60 minutes
solver.add(brian_meeting_start >= 450)  # 3:30 PM in minutes
solver.add(brian_meeting_start + 60 <= 585)  # 9:45 PM in minutes

# Kenneth: 9:45 AM to 9:00 PM, 30 minutes
solver.add(kenneth_meeting_start >= 585)  # 9:45 AM in minutes
solver.add(kenneth_meeting_start + 30 <= 540)  # 9:00 PM in minutes

# Jason: 8:15 AM to 11:45 AM, 75 minutes
solver.add(jason_meeting_start >= 495)  # 8:15 AM in minutes
solver.add(jason_meeting_start + 75 <= 685)  # 11:45 AM in minutes

# Stephanie: 2:45 PM to 6:45 PM, 105 minutes
solver.add(stephanie_meeting_start >= 345)  # 2:45 PM in minutes
solver.add(stephanie_meeting_start + 105 <= 405)  # 6:45 PM in minutes

# Kimberly: 9:45 AM to 7:30 PM, 75 minutes
solver.add(kimberly_meeting_start >= 585)  # 9:45 AM in minutes
solver.add(kimberly_meeting_start + 75 <= 450)  # 7:30 PM in minutes

# Steven: 7:15 AM to 9:15 PM, 60 minutes
solver.add(steven_meeting_start >= 435)  # 7:15 AM in minutes
solver.add(steven_meeting_start + 60 <= 555)  # 9:15 PM in minutes

# Mark: 10:15 AM to 1:00 PM, 75 minutes
solver.add(mark_meeting_start >= 615)  # 10:15 AM in minutes
solver.add(mark_meeting_start + 75 <= 660)  # 1:00 PM in minutes

# Ensure no overlapping meetings
locations = {
    'karen': 'Haight-Ashbury',
    'jessica': 'Nob Hill',
    'brian': 'Russian Hill',
    'kenneth': 'North Beach',
    'jason': 'Chinatown',
    'stephanie': 'Union Square',
    'kimberly': 'Embarcadero',
    'steven': 'Financial District',
    'mark': 'Marina District'
}

travel_times = {
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Marina District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Marina District'): 12,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17
}

# Start from Presidio at 9:00 AM (0 minutes)
current_location = 'Presidio'
current_time = 0

# Function to add travel time constraints
def add_travel_constraints(prev_location, prev_time, next_location, next_meeting_start):
    travel_time = travel_times[(prev_location, next_location)]
    solver.add(next_meeting_start >= prev_time + travel_time)

# Define the order of meetings
meetings = [
    ('jason', jason_meeting_start, 75),
    ('mark', mark_meeting_start, 75),
    ('kenneth', kenneth_meeting_start, 30),
    ('stephanie', stephanie_meeting_start, 105),
    ('kimberly', kimberly_meeting_start, 75),
    ('steven', steven_meeting_start, 60),
    ('brian', brian_meeting_start, 60),
    ('jessica', jessica_meeting_start, 90),
    ('karen', karen_meeting_start, 45)
]

# Add travel constraints for each meeting
for i in range(len(meetings) - 1):
    prev_location, prev_time, _ = meetings[i]
    next_location, next_meeting_start, _ = meetings[i + 1]
    add_travel_constraints(prev_location, prev_time + meetings[i][2], next_location, next_meeting_start)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for name, start, duration in meetings:
        print(f"{name}: {model[start]} - {model[start] + duration}")
else:
    print("No solution found")