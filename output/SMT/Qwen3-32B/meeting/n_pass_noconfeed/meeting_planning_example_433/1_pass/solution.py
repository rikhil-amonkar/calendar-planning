import json
from z3 import *

# Define friends and their information
friends_info = {
    1: {'name': 'Emily', 'available_start': 1140, 'available_end': 1260, 'min_duration': 15},
    2: {'name': 'Margaret', 'available_start': 990, 'available_end': 1215, 'min_duration': 75},
    3: {'name': 'Ronald', 'available_start': 1110, 'available_end': 1170, 'min_duration': 45},
    4: {'name': 'Deborah', 'available_start': 825, 'available_end': 1275, 'min_duration': 90},
    5: {'name': 'Jeffrey', 'available_start': 675, 'available_end': 870, 'min_duration': 120},
}

# Define travel time function in Z3
def travel_time(source, dest):
    return If(
        source == 0,
        If(dest == 0, 0,
           If(dest == 1, 14,
              If(dest == 2, 9,
                 If(dest == 3, 8,
                    If(dest == 4, 17,
                       If(dest == 5, 17, 0)))))),
        If(source == 1,
           If(dest == 0, 17,
              If(dest == 1, 0,
                 If(dest == 2, 22,
                    If(dest == 3, 17,
                       If(dest == 4, 16,
                          If(dest == 5, 9, 0)))))),
           If(source == 2,
              If(dest == 0, 8,
                 If(dest == 1, 21,
                    If(dest == 2, 0,
                       If(dest == 3, 7,
                          If(dest == 4, 23,
                             If(dest == 5, 23, 0)))))),
              If(source == 3,
                 If(dest == 0, 7,
                    If(dest == 1, 18,
                       If(dest == 2, 8,
                          If(dest == 3, 0,
                             If(dest == 4, 22,
                                If(dest == 5, 22, 0)))))),
                 If(source == 4,
                    If(dest == 0, 16,
                       If(dest == 1, 16,
                          If(dest == 2, 20,
                             If(dest == 3, 20,
                                If(dest == 4, 0,
                                   If(dest == 5, 11, 0)))))),
                    If(source == 5,
                       If(dest == 0, 20,
                          If(dest == 1, 7,
                             If(dest == 2, 26,
                                If(dest == 3, 24,
                                   If(dest == 4, 13,
                                      If(dest == 5, 0, 0)))))),
                       0)))))

num_steps = 5
s = Optimize()

# Create variables for each step's friend, start, end
friend_vars = [Int('friend_{}'.format(i)) for i in range(num_steps)]
start_vars = [Int('start_{}'.format(i)) for i in range(num_steps)]
end_vars = [Int('end_{}'.format(i)) for i in range(num_steps)]

# Initial prev_location and prev_time
prev_location = 0
prev_time = 540  # 9:00 AM in minutes

for i in range(num_steps):
    friend_i = friend_vars[i]
    start_i = start_vars[i]
    end_i = end_vars[i]

    # Friend can be 0 or 1-5
    s.add(Or(friend_i == 0, And(1 <= friend_i, friend_i <= 5)))

    # Add constraints for this step based on prev_location and prev_time
    for f in range(1, 6):  # friends 1-5
        cond = And(friend_i == f, friend_i != 0)
        # Travel time from previous location to current friend's location (f)
        tt = travel_time(prev_location, f)
        s.add(Implies(cond, start_i >= prev_time + tt))
        # Available start time
        s.add(Implies(cond, start_i >= friends_info[f]['available_start']))
        # End time is start + duration
        s.add(Implies(cond, end_i == start_i + friends_info[f]['min_duration']))
        # End time <= available end
        s.add(Implies(cond, end_i <= friends_info[f]['available_end']))

    # Update prev_location and prev_time for next step
    next_prev_location = If(friend_i != 0, friend_i, prev_location)
    next_prev_time = If(friend_i != 0, end_i, prev_time)
    prev_location = next_prev_location
    prev_time = next_prev_time

# Ensure no duplicate friends
for i in range(num_steps):
    for j in range(i + 1, num_steps):
        s.add(Or(friend_vars[i] == 0, friend_vars[j] == 0, friend_vars[i] != friend_vars[j]))

# Maximize the number of friends met
count = Sum([If(friend_vars[i] != 0, 1, 0) for i in range(num_steps)])
s.maximize(count)

# Check if a solution exists
if s.check() == sat:
    m = s.model()
    # Extract the meetings
    meetings = []
    for i in range(num_steps):
        friend = m.eval(friend_vars[i])
        if friend != 0:
            start = m.eval(start_vars[i])
            end = m.eval(end_vars[i])
            name = friends_info[friend]['name']
            location = {
                1: 'Richmond District',
                2: 'Financial District',
                3: 'North Beach',
                4: 'The Castro',
                5: 'Golden Gate Park'
            }[friend]
            # Convert start and end to H:MM format
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h}:{m:02d}"
            start_str = to_time_str(start)
            end_str = to_time_str(end)
            meetings.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Output as JSON
    result = {"itinerary": meetings}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))