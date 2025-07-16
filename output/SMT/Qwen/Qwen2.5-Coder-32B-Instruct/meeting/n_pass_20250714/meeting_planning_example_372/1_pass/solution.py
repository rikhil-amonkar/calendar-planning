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

# Add constraints for travel times between meetings
for i in range(len(locations)):
    for j in range(len(locations)):
        if i != j:
            for friend1 in availability:
                for friend2 in availability:
                    if friend1 != friend2:
                        # If friend1 meets friend2, they must have enough time to travel between them
                        solver.add(
                            Or(
                                time_slot_vars[friend1] + meeting_durations[friend1] <= time_slot_vars[friend2],
                                time_slot_vars[friend2] + meeting_durations[friend2] <= time_slot_vars[friend1],
                                Abs(time_slot_vars[friend1] - time_slot_vars[friend2]) >= travel_times[(locations[i], locations[j])]
                            )
                        )

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {friend: (locations[model[location_vars[friend]].as_long()], model[time_slot_vars[friend]].as_long()) for friend in availability}
    print("SOLUTION:")
    for friend, (location, time_slot) in solution.items():
        hours = time_slot // 60
        minutes = time_slot % 60
        print(f"Meet {friend} at {location} from {hours:02}:{minutes:02} to {hours + meeting_durations[friend] // 60:02}:{(minutes + meeting_durations[friend] % 60) % 60:02}")
else:
    print("No solution found.")