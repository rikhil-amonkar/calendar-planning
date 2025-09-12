from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Ronald',
        'location': 'Nob Hill',
        'available_start': 600,  # 10:00 AM
        'available_end': 1020,   # 5:00 PM
        'required': 105
    },
    {
        'name': 'Sarah',
        'location': 'Russian Hill',
        'available_start': 435,  # 7:15 AM
        'available_end': 570,    # 9:30 AM
        'required': 45
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'available_start': 810,  # 1:30 PM
        'available_end': 1080,   # 5:00 PM
        'required': 120
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'available_start': 855,  # 2:15 PM
        'available_end': 1110,   # 7:30 PM
        'required': 90
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'available_start': 615,  # 10:15 AM
        'available_end': 1080,   # 10:00 PM
        'required': 60
    },
]

travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

# Precompute travel times between friends
travel_times_between_friends = [[0 for _ in range(5)] for _ in range(5)]
for prev in range(5):
    for curr in range(5):
        prev_loc = friends[prev]['location']
        curr_loc = friends[curr]['location']
        travel_times_between_friends[prev][curr] = travel_times[(prev_loc, curr_loc)]

solver = Optimize()

is_used = [Bool(f'is_used_{i}') for i in range(5)]
friend = [Int(f'friend_{i}') for i in range(5)]
start = [Int(f'start_{i}') for i in range(5)]
end = [Int(f'end_{i}') for i in range(5)]

# Constraints for each step
for i in range(5):
    # If is_used[i], then friend[i] is between 0 and 4
    solver.add(Implies(is_used[i], And(friend[i] >= 0, friend[i] <= 4)))

# Step 0 constraints
def get_travel_time_pacific_heights(friend_idx):
    return If(friend_idx == 0, 8,
              If(friend_idx == 1, 7,
                 If(friend_idx == 2, 16,
                    If(friend_idx == 3, 21,
                       If(friend_idx == 4, 11, 0)))))

travel_time_0 = get_travel_time_pacific_heights(friend[0])
start_0 = 540 + travel_time_0  # arrival time is 9:00 AM = 540 min
duration_0 = If(friend[0] == 0, 105,
                If(friend[0] == 1, 45,
                   If(friend[0] == 2, 120,
                      If(friend[0] == 3, 90,
                         If(friend[0] == 4, 60, 0)))))

end_0 = start_0 + duration_0

available_start_0 = If(friend[0] == 0, 600,
                       If(friend[0] == 1, 435,
                          If(friend[0] == 2, 810,
                             If(friend[0] == 3, 855,
                                If(friend[0] == 4, 615, 0)))))

available_end_0 = If(friend[0] == 0, 1020,
                     If(friend[0] == 1, 570,
                        If(friend[0] == 2, 1080,
                           If(friend[0] == 3, 1110,
                              If(friend[0] == 4, 1080, 0)))))

solver.add(Implies(is_used[0], start[0] == start_0))
solver.add(Implies(is_used[0], end[0] == end_0))
solver.add(Implies(is_used[0], start[0] >= available_start_0))
solver.add(Implies(is_used[0], end[0] <= available_end_0))

# Steps 1-4
for i in range(1, 5):
    # is_used[i] implies is_used[i-1]
    solver.add(Implies(is_used[i], is_used[i-1]))

    # Compute travel time between friends[i-1] and friends[i]
    def get_travel_time_between_friends(friend_prev, friend_curr):
        t0 = If(friend_curr == 0, travel_times_between_friends[0][0],
                If(friend_curr == 1, travel_times_between_friends[0][1],
                   If(friend_curr == 2, travel_times_between_friends[0][2],
                      If(friend_curr == 3, travel_times_between_friends[0][3],
                         If(friend_curr == 4, travel_times_between_friends[0][4], 0)))))
        t1 = If(friend_curr == 0, travel_times_between_friends[1][0],
                If(friend_curr == 1, travel_times_between_friends[1][1],
                   If(friend_curr == 2, travel_times_between_friends[1][2],
                      If(friend_curr == 3, travel_times_between_friends[1][3],
                         If(friend_curr == 4, travel_times_between_friends[1][4], 0)))))
        t2 = If(friend_curr == 0, travel_times_between_friends[2][0],
                If(friend_curr == 1, travel_times_between_friends[2][1],
                   If(friend_curr == 2, travel_times_between_friends[2][2],
                      If(friend_curr == 3, travel_times_between_friends[2][3],
                         If(friend_curr == 4, travel_times_between_friends[2][4], 0)))))
        t3 = If(friend_curr == 0, travel_times_between_friends[3][0],
                If(friend_curr == 1, travel_times_between_friends[3][1],
                   If(friend_curr == 2, travel_times_between_friends[3][2],
                      If(friend_curr == 3, travel_times_between_friends[3][3],
                         If(friend_curr == 4, travel_times_between_friends[3][4], 0)))))
        t4 = If(friend_curr == 0, travel_times_between_friends[4][0],
                If(friend_curr == 1, travel_times_between_friends[4][1],
                   If(friend_curr == 2, travel_times_between_friends[4][2],
                      If(friend_curr == 3, travel_times_between_friends[4][3],
                         If(friend_curr == 4, travel_times_between_friends[4][4], 0)))))
        return If(friend_prev == 0, t0,
                  If(friend_prev == 1, t1,
                     If(friend_prev == 2, t2,
                        If(friend_prev == 3, t3,
                           If(friend_prev == 4, t4, 0)))))

    travel_time_i = get_travel_time_between_friends(friend[i-1], friend[i])
    start_i = end[i-1] + travel_time_i
    duration_i = If(friend[i] == 0, 105,
                    If(friend[i] == 1, 45,
                       If(friend[i] == 2, 120,
                          If(friend[i] == 3, 90,
                             If(friend[i] == 4, 60, 0)))))
    end_i = start_i + duration_i
    available_start_i = If(friend[i] == 0, 600,
                           If(friend[i] == 1, 435,
                              If(friend[i] == 2, 810,
                                 If(friend[i] == 3, 855,
                                    If(friend[i] == 4, 615, 0)))))
    available_end_i = If(friend[i] == 0, 1020,
                         If(friend[i] == 1, 570,
                            If(friend[i] == 2, 1080,
                               If(friend[i] == 3, 1110,
                                  If(friend[i] == 4, 1080, 0)))))

    solver.add(Implies(is_used[i], start[i] == start_i))
    solver.add(Implies(is_used[i], end[i] == end_i))
    solver.add(Implies(is_used[i], start[i] >= available_start_i))
    solver.add(Implies(is_used[i], end[i] <= available_end_i))

# Add constraints that no two steps have the same friend (if used)
for i in range(5):
    for j in range(i+1, 5):
        solver.add(Implies(And(is_used[i], is_used[j]), friend[i] != friend[j]))

# Objective: maximize the number of used steps
num_used = Sum([If(is_used[i], 1, 0) for i in range(5)])
solver.maximize(num_used)

# Check for solution
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(5):
        if is_used[i] and model.eval(is_used[i]):
            friend_idx = model.eval(friend[i]).as_long()
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            name = friends[friend_idx]['name']
            itinerary.append({
                "action": "meet",
                "location": friends[friend_idx]['location'],
                "person": name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")