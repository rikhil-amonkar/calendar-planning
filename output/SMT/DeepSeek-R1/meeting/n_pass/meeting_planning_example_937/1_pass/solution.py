from z3 import *

# Define locations in the order they appear in the problem
locations = [
    'Russian Hill',
    'Sunset District',
    'Union Square',
    'Nob Hill',
    'Marina District',
    'Richmond District',
    'Financial District',
    'Embarcadero',
    'The Castro',
    'Alamo Square',
    'Presidio'
]

# Travel time data for each location to the other 10 locations (in order of increasing index, skipping itself)
data = [
    [23, 10, 5, 7, 14, 11, 8, 21, 15, 14],    # Russian Hill
    [24, 30, 27, 21, 12, 30, 30, 17, 17, 16],  # Sunset District
    [13, 27, 9, 18, 20, 9, 11, 17, 15, 24],    # Union Square
    [5, 24, 7, 11, 14, 9, 9, 17, 11, 17],      # Nob Hill
    [8, 19, 16, 12, 11, 17, 14, 22, 15, 10],   # Marina District
    [13, 11, 21, 17, 9, 22, 19, 16, 13, 7],    # Richmond District
    [11, 30, 9, 8, 15, 21, 4, 20, 17, 22],     # Financial District
    [8, 30, 10, 10, 12, 21, 5, 25, 19, 20],    # Embarcadero
    [18, 17, 19, 16, 21, 16, 21, 22, 8, 20],   # The Castro
    [13, 16, 14, 11, 15, 11, 17, 16, 8, 17],   # Alamo Square
    [14, 15, 22, 18, 11, 7, 23, 20, 21, 19]    # Presidio
]

# Build travel_times dictionary
travel_times = {}
for loc in locations:
    travel_times[loc] = {}

for idx_i, loc_i in enumerate(locations):
    row = data[idx_i]
    dest_indices = [j for j in range(len(locations)) if j != idx_i]
    for k, j in enumerate(dest_indices):
        loc_j = locations[j]
        travel_times[loc_i][loc_j] = row[k]

# Friends data: (name, location, start_avail (minutes from 9AM), end_avail (minutes from 9AM), min_duration)
friends_data = [
    ('David', 'Sunset District', 15, 765, 15),
    ('Kenneth', 'Union Square', 735, 765, 15),
    ('Patricia', 'Nob Hill', 360, 615, 120),
    ('Mary', 'Marina District', 345, 465, 45),
    ('Charles', 'Richmond District', 495, 720, 15),
    ('Joshua', 'Financial District', 330, 495, 90),
    ('Ronald', 'Embarcadero', 555, 705, 30),
    ('George', 'The Castro', 315, 600, 105),
    ('Kimberly', 'Alamo Square', 0, 330, 105),
    ('William', 'Presidio', 0, 225, 60)
]

s = Optimize()

# Create variables for each friend
meet_vars = {}
start_vars = {}
end_vars = {}

for name, loc, s_avail, e_avail, dur in friends_data:
    meet_vars[name] = Bool(name)
    start_vars[name] = Int(f"start_{name}")
    end_vars[name] = start_vars[name] + dur

# Constraints for each friend: if meeting, then within time window
for name, loc, s_avail, e_avail, dur in friends_data:
    s.add(Implies(meet_vars[name], start_vars[name] >= s_avail))
    s.add(Implies(meet_vars[name], end_vars[name] <= e_avail))

# Constraint: travel time from Russian Hill to first meeting location
for name, loc, s_avail, e_avail, dur in friends_data:
    travel_time = travel_times['Russian Hill'][loc]
    s.add(Implies(meet_vars[name], start_vars[name] >= travel_time))

# Disjunctive constraints for every pair of friends
n = len(friends_data)
for i in range(n):
    name_i, loc_i, s_avail_i, e_avail_i, dur_i = friends_data[i]
    for j in range(i+1, n):
        name_j, loc_j, s_avail_j, e_avail_j, dur_j = friends_data[j]
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        s.add(Implies(And(meet_vars[name_i], meet_vars[name_j]),
                     Or(end_vars[name_i] + travel_ij <= start_vars[name_j],
                        end_vars[name_j] + travel_ji <= start_vars[name_i])))

# Maximize the number of friends met
total_met = Sum([If(meet_vars[name], 1, 0) for name in meet_vars])
s.maximize(total_met)

# Solve the problem
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    schedule = []
    for name, loc, s_avail, e_avail, dur in friends_data:
        if is_true(m.eval(meet_vars[name])):
            start_val = m.eval(start_vars[name]).as_long()
            total_minutes = start_val
            hours = total_minutes // 60
            minutes = total_minutes % 60
            abs_hour = 9 + hours
            if abs_hour >= 13:
                hour = abs_hour - 12
                am_pm = "PM"
            elif abs_hour == 12:
                hour = 12
                am_pm = "PM"
            else:
                hour = abs_hour
                am_pm = "AM"
            end_time = start_val + dur
            end_hours = end_time // 60
            end_minutes = end_time % 60
            abs_end_hour = 9 + end_hours
            if abs_end_hour >= 13:
                end_hour = abs_end_hour - 12
                end_am_pm = "PM"
            elif abs_end_hour == 12:
                end_hour = 12
                end_am_pm = "PM"
            else:
                end_hour = abs_end_hour
                end_am_pm = "AM"
            schedule.append((start_val, name, loc, hour, minutes, am_pm, end_hour, end_minutes, end_am_pm, dur))
    
    schedule.sort()
    for entry in schedule:
        start_val, name, loc, hour, minutes, am_pm, end_hour, end_minutes, end_am_pm, dur = entry
        print(f"Meet {name} at {loc} from {hour}:{minutes:02d} {am_pm} to {end_hour}:{end_minutes:02d} {end_am_pm} (for {dur} minutes)")
    print(f"Total friends met: {len(schedule)}")
else:
    print("No solution found")