import json
from z3 import *

# Define travel_time dictionary
travel_time = {
    'Marina District': {
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8
    },
    'Mission District': {
        'Marina District': 19,
        'Fisherman\'s Wharf': 22,
        'Presidio': 25,
        'Union Square': 15,
        'Sunset District': 24,
        'Financial District': 15,
        'Haight-Ashbury': 12,
        'Russian Hill': 15
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Mission District': 22,
        'Presidio': 17,
        'Union Square': 13,
        'Sunset District': 27,
        'Financial District': 11,
        'Haight-Ashbury': 22,
        'Russian Hill': 7
    },
    'Presidio': {
        'Marina District': 11,
        'Mission District': 26,
        'Fisherman\'s Wharf': 19,
        'Union Square': 22,
        'Sunset District': 15,
        'Financial District': 23,
        'Haight-Ashbury': 15,
        'Russian Hill': 14
    },
    'Union Square': {
        'Marina District': 18,
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Presidio': 24,
        'Sunset District': 27,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Russian Hill': 13
    },
    'Sunset District': {
        'Marina District': 21,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Presidio': 16,
        'Union Square': 30,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Russian Hill': 24
    },
    'Financial District': {
        'Marina District': 15,
        'Mission District': 17,
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Union Square': 9,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Russian Hill': 11
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Mission District': 11,
        'Fisherman\'s Wharf': 23,
        'Presidio': 15,
        'Union Square': 19,
        'Sunset District': 15,
        'Financial District': 21,
        'Russian Hill': 17
    },
    'Russian Hill': {
        'Marina District': 7,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Presidio': 14,
        'Union Square': 10,
        'Sunset District': 23,
        'Financial District': 11,
        'Haight-Ashbury': 17
    }
}

# List of events: 8 friends + 1 dummy event at the start
events = [
    # (name, location, duration, availability_start, availability_end) in minutes from 9:00 AM
    ('Karen', 'Mission District', 30, 315, 780),      # 2:15PM to 10:00PM
    ('Richard', 'Fisherman\'s Wharf', 30, 330, 510),  # 2:30PM to 5:30PM
    ('Robert', 'Presidio', 60, 765, 825),             # 9:45PM to 10:45PM
    ('Joseph', 'Union Square', 120, 165, 345),        # 11:45AM to 2:45PM
    ('Helen', 'Sunset District', 105, 345, 705),      # 2:45PM to 8:45PM
    ('Elizabeth', 'Financial District', 75, 60, 225), # 10:00AM to 12:45PM
    ('Kimberly', 'Haight-Ashbury', 105, 315, 510),    # 2:15PM to 5:30PM
    ('Ashley', 'Russian Hill', 45, 150, 750),         # 11:30AM to 9:30PM
    ('dummy', 'Marina District', 0, 0, 0)             # Dummy event at start
]

n_total = len(events)  # 9 events: 8 friends + 1 dummy

# Create optimizer for maximization
opt = Optimize()

# For each event: meet variable (for the first 8, the friends; dummy is always met)
meet = []
for i in range(n_total - 1):  # first 8 are friends
    meet.append(Bool(f'meet_{i}'))
meet.append(True)  # dummy is always met

# Start and end times for each event
start = [Int(f'start_{i}') for i in range(n_total)]
end = [Int(f'end_{i}') for i in range(n_total)]

# Dummy event is fixed at time 0
opt.add(start[8] == 0)
opt.add(end[8] == 0)

# For each friend event, set end = start + duration
for i in range(n_total - 1):  # skip dummy
    opt.add(end[i] == start[i] + events[i][2])

# For each friend, if met, then within availability window
for i in range(n_total - 1):
    name, loc, dur, avail_start, avail_end = events[i]
    opt.add(Implies(meet[i], And(start[i] >= avail_start, end[i] <= avail_end)))

# Disjunctive constraints for every pair of events (including dummy)
for i in range(n_total):
    for j in range(i + 1, n_total):
        loc_i = events[i][1]
        loc_j = events[j][1]
        t_ij = travel_time[loc_i][loc_j]
        t_ji = travel_time[loc_j][loc_i]
        # Condition: both events are met
        cond = And(meet[i], meet[j])
        # Disjunctive constraint: either j starts after i ends plus travel time, or i starts after j ends plus travel time
        opt.add(Implies(cond, Or(start[j] >= end[i] + t_ij, start[i] >= end[j] + t_ji)))

# Maximize the number of friends met (excluding dummy)
num_meetings = Sum([If(meet[i], 1, 0) for i in range(8)])
opt.maximize(num_meetings)

# Check if a solution exists
if opt.check() == sat:
    model = opt.model()
    itinerary_list = []
    base_hour = 9  # starting at 9:00 AM

    for i in range(8):  # only for friends, not dummy
        if model.evaluate(meet[i]):
            start_val = model.evaluate(start[i])
            end_val = model.evaluate(end[i])
            if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                total_minutes_start = start_val.as_long()
                hours_start = total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                abs_hour_start = base_hour + hours_start
                abs_minute_start = minutes_start
                start_time = f"{abs_hour_start}:{abs_minute_start:02d}"

                total_minutes_end = end_val.as_long()
                hours_end = total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                abs_hour_end = base_hour + hours_end
                abs_minute_end = minutes_end
                end_time = f"{abs_hour_end}:{abs_minute_end:02d}"

                itinerary_list.append({
                    "action": "meet",
                    "person": events[i][0],
                    "start_time": start_time,
                    "end_time": end_time
                })
    
    # Sort itinerary by start_time
    itinerary_list.sort(key=lambda x: x['start_time'])
    
    # Output the solution
    print("SOLUTION:")
    print('{"itinerary": ' + json.dumps(itinerary_list) + '}')
else:
    print("SOLUTION:")
    print('{"itinerary": []}')