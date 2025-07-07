from z3 import *

# Define the time slots in minutes from 9:00 AM to 10:00 PM
time_slots = list(range(540, 1200))  # 540 minutes is 9:00 AM, 1200 minutes is 10:00 PM

# Define the locations
locations = ['Sunset District', 'Alamo Square', 'Russian Hill', 'Golden Gate Park', 'Mission District']

# Define the travel times
travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
}

# Define the availability and meeting duration constraints
availability = {
    'Charles': {'location': 'Alamo Square', 'start': 1080, 'end': 1125},  # 6:00 PM to 8:45 PM
    'Margaret': {'location': 'Russian Hill', 'start': 540, 'end': 840},  # 9:00 AM to 4:00 PM
    'Daniel': {'location': 'Golden Gate Park', 'start': 480, 'end': 750},  # 8:00 AM to 1:30 PM
    'Stephanie': {'location': 'Mission District', 'start': 1050, 'end': 1140},  # 8:30 PM to 10:00 PM
}

meeting_durations = {
    'Charles': 90,
    'Margaret': 30,
    'Daniel': 15,
    'Stephanie': 90,
}

# Create a solver instance
solver = Solver()

# Define variables for the location and time slot for each friend
location_vars = {friend: Int(friend + '_location') for friend in availability}
time_slot_vars = {friend: Int(friend + '_time_slot') for friend in availability}

# Add constraints for each friend
for friend, info in availability.items():
    location = info['location']
    start = info['start']
    end = info['end']
    duration = meeting_durations[friend]
    
    # Friend must be at their location during their availability
    solver.add(location_vars[friend] == locations.index(location))
    solver.add(time_slot_vars[friend] >= start)
    solver.add(time_slot_vars[friend] <= end - duration + 1)

# Ensure each friend is met exactly once
friends = list(availability.keys())
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend1 = friends[i]
        friend2 = friends[j]
        
        # Ensure no two friends are met at the same time
        solver.add(
            Or(
                time_slot_vars[friend1] + meeting_durations[friend1] <= time_slot_vars[friend2],
                time_slot_vars[friend2] + meeting_durations[friend2] <= time_slot_vars[friend1]
            )
        )
        
        # Ensure travel time between meetings is respected
        solver.add(
            Abs(time_slot_vars[friend1] - time_slot_vars[friend2]) >= travel_times[(locations[location_vars[friend1].as_long()], locations[location_vars[friend2].as_long()])]
        )

# Manually check feasible schedules
def check_schedule(schedule):
    for i in range(len(schedule) - 1):
        friend1 = schedule[i]
        friend2 = schedule[i + 1]
        loc1 = availability[friend1]['location']
        loc2 = availability[friend2]['location']
        ts1 = schedule_time[friend1]
        ts2 = schedule_time[friend2]
        dur1 = meeting_durations[friend1]
        dur2 = meeting_durations[friend2]
        
        if ts1 + dur1 > ts2 or ts2 + dur2 > ts1:
            return False
        
        if abs(ts1 - ts2) < travel_times[(loc1, loc2)]:
            return False
    
    return True

# Try different permutations of the schedule
from itertools import permutations

schedule_time = {}
for perm in permutations(friends):
    schedule_time.clear()
    current_time = 540  # Start at 9:00 AM
    valid = True
    for friend in perm:
        loc = availability[friend]['location']
        start = availability[friend]['start']
        end = availability[friend]['end']
        dur = meeting_durations[friend]
        
        # Find a valid time slot for the friend
        found = False
        for ts in range(start, end - dur + 1):
            if ts >= current_time + travel_times[(locations[location_vars[perm[0]].as_long()], loc)]:
                schedule_time[friend] = ts
                current_time = ts + dur
                found = True
                break
        
        if not found:
            valid = False
            break
    
    if valid and check_schedule(perm):
        print("SOLUTION:")
        for friend in perm:
            ts = schedule_time[friend]
            loc = availability[friend]['location']
            dur = meeting_durations[friend]
            hours = ts // 60
            minutes = ts % 60
            print(f"Meet {friend} at {loc} from {hours:02}:{minutes:02} to {hours + dur // 60:02}:{(minutes + dur % 60) % 60:02}")
        break
else:
    print("No solution found.")