from z3 import *

# Define the time slots in minutes from 9:00AM to 10:00PM
start_time = 9 * 60  # 9:00 AM
end_time = 22 * 60   # 10:00 PM
time_slots = list(range(start_time, end_time + 1))

# Define the travel times
travel_times = {
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Alamo Square'): 19,
}

# Define the availability and meeting duration requirements
availability = {
    'David': (9 * 60 + 15, 22 * 60, 15),
    'Kenneth': (21 * 60 + 15, 21 * 60 + 45, 15),
    'Patricia': (15 * 60, 19 * 60 + 15, 120),
    'Mary': (14 * 60 + 45, 16 * 60 + 45, 45),
    'Charles': (17 * 60 + 15, 21 * 60, 15),
    'Joshua': (14 * 60 + 30, 17 * 60 + 15, 90),
    'Ronald': (18 * 60 + 15, 20 * 60 + 45, 30),
    'George': (14 * 60 + 15, 19 * 60, 105),
    'Kimberly': (9 * 60, 14 * 60 + 30, 105),
    'William': (7 * 60, 12 * 60 + 45, 60),
}

# Create a solver instance
solver = Solver()

# Define the decision variables
locations = ['Russian Hill', 'Sunset District', 'Union Square', 'Nob Hill', 'Marina District', 'Richmond District', 'Financial District', 'Embarcadero', 'The Castro', 'Alamo Square', 'Presidio']
current_location = String('current_location')
next_location = String('next_location')
start_time_var = Int('start_time_var')
end_time_var = Int('end_time_var')

# Add constraints for each friend
for friend, (avail_start, avail_end, min_duration) in availability.items():
    friend_start = Int(f'{friend}_start')
    friend_end = Int(f'{friend}_end')
    solver.add(friend_start >= avail_start)
    solver.add(friend_end <= avail_end)
    solver.add(friend_end - friend_start >= min_duration)

# Add constraints for travel times and location changes
current_loc = 'Russian Hill'
current_time = start_time

for friend, (avail_start, avail_end, min_duration) in availability.items():
    next_loc = String(f'{friend}_location')
    solver.add(next_loc == Or([StringVal(loc) for loc in locations]))
    solver.add(next_loc != current_loc)
    travel_time = Int(f'travel_time_{friend}')
    solver.add(travel_time == travel_times[(current_loc, next_loc)])
    solver.add(current_time + travel_time <= avail_start)
    solver.add(avail_start + min_duration <= avail_end)
    current_loc = next_loc
    current_time = avail_start + min_duration

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, (avail_start, avail_end, min_duration) in availability.items():
        start = model[Int(f'{friend}_start')].as_long()
        end = model[Int(f'{friend}_end')].as_long()
        location = model[String(f'{friend}_location')].as_string()
        print(f"Meet {friend} at {location} from {start // 60}:{start % 60:02d} to {end // 60}:{end % 60:02d}")
else:
    print("No solution found")