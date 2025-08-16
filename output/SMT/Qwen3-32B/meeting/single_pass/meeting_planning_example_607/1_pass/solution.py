from z3 import *
import json

# Define friends and their parameters
friends = [
    {
        'name': 'Karen',
        'district': 1,  # Russian Hill
        'available_start': 20 * 60 + 45,  # 20:45
        'available_end': 21 * 60 + 45,    # 21:45
        'required_duration': 60
    },
    {
        'name': 'Jessica',
        'district': 2,  # The Castro
        'available_start': 15 * 60 + 45,  # 15:45
        'available_end': 19 * 60 + 30,    # 19:30
        'required_duration': 60
    },
    {
        'name': 'Matthew',
        'district': 3,  # Richmond District
        'available_start': 7 * 60 + 30,   # 7:30
        'available_end': 15 * 60 + 15,    # 15:15
        'required_duration': 15
    },
    {
        'name': 'Michelle',
        'district': 4,  # Marina District
        'available_start': 10 * 60 + 30,  # 10:30
        'available_end': 18 * 60 + 45,    # 18:45
        'required_duration': 75
    },
    {
        'name': 'Carol',
        'district': 5,  # North Beach
        'available_start': 12 * 60 + 0,   # 12:00
        'available_end': 17 * 60 + 0,     # 17:00
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'district': 6,  # Union Square
        'available_start': 10 * 60 + 45,  # 10:45
        'available_end': 14 * 60 + 15,    # 14:15
        'required_duration': 30
    },
    {
        'name': 'Linda',
        'district': 7,  # Golden Gate Park
        'available_start': 10 * 60 + 45,  # 10:45
        'available_end': 22 * 60 + 0,     # 22:00
        'required_duration': 90
    }
]

# Define travel_time_matrix for districts 0 (Sunset) to 7 (Golden Gate Park)
travel_time_matrix = [
    [0, 24, 17, 12, 21, 29, 30, 11],
    [23, 0, 21, 14, 7, 5, 11, 21],
    [17, 18, 0, 16, 21, 20, 19, 11],
    [11, 13, 16, 0, 9, 17, 21, 9],
    [19, 8, 22, 11, 0, 11, 16, 18],
    [27, 4, 22, 18, 9, 0, 7, 22],
    [26, 13, 19, 20, 18, 10, 0, 22],
    [10, 19, 13, 7, 16, 24, 22, 0]
]

# Number of positions in the itinerary
positions = 7

# Create Z3 variables
friends_vars = [Int(f'friend_{i}') for i in range(positions)]
start_vars = [Int(f'start_{i}') for i in range(positions)]
end_vars = [Int(f'end_{i}') for i in range(positions)]

solver = Optimize()

# Add constraints for friends_vars to be between -1 and 6
for f in friends_vars:
    solver.add(And(f >= -1, f <= 6))

# Add uniqueness constraints for friends
for i in range(positions):
    for j in range(i + 1, positions):
        solver.add(Or(friends_vars[i] == -1, friends_vars[j] == -1, friends_vars[i] != friends_vars[j]))

# Function to get district from friend index
def get_district(friend_index):
    return If(friend_index == 0, 1,
              If(friend_index == 1, 2,
                 If(friend_index == 2, 3,
                    If(friend_index == 3, 4,
                       If(friend_index == 4, 5,
                          If(friend_index == 5, 6,
                             If(friend_index == 6, 7, 0))))))

# Function to get travel time between two districts
def get_travel_time(from_district, to_district):
    return If(from_district == 0,
              If(to_district == 0, 0,
                 If(to_district == 1, 24,
                    If(to_district == 2, 17,
                       If(to_district == 3, 12,
                          If(to_district == 4, 21,
                             If(to_district == 5, 29,
                                If(to_district == 6, 30,
                                   If(to_district == 7, 11, 0))))))),
              If(from_district == 1,
                 If(to_district == 0, 23,
                    If(to_district == 1, 0,
                       If(to_district == 2, 21,
                          If(to_district == 3, 14,
                             If(to_district == 4, 7,
                                If(to_district == 5, 5,
                                   If(to_district == 6, 11,
                                      If(to_district == 7, 21, 0)))))),
                 If(from_district == 2,
                    If(to_district == 0, 17,
                       If(to_district == 1, 18,
                          If(to_district == 2, 0,
                             If(to_district == 3, 16,
                                If(to_district == 4, 21,
                                   If(to_district == 5, 20,
                                      If(to_district == 6, 19,
                                         If(to_district == 7, 11, 0)))))),
                    If(from_district == 3,
                       If(to_district == 0, 11,
                          If(to_district == 1, 13,
                             If(to_district == 2, 16,
                                If(to_district == 3, 0,
                                   If(to_district == 4, 9,
                                      If(to_district == 5, 17,
                                         If(to_district == 6, 21,
                                            If(to_district == 7, 9, 0)))))),
                       If(from_district == 4,
                          If(to_district == 0, 19,
                             If(to_district == 1, 8,
                                If(to_district == 2, 22,
                                   If(to_district == 3, 11,
                                      If(to_district == 4, 0,
                                         If(to_district == 5, 11,
                                            If(to_district == 6, 16,
                                               If(to_district == 7, 18, 0)))))),
                          If(from_district == 5,
                             If(to_district == 0, 27,
                                If(to_district == 1, 4,
                                   If(to_district == 2, 22,
                                      If(to_district == 3, 18,
                                         If(to_district == 4, 9,
                                            If(to_district == 5, 0,
                                               If(to_district == 6, 7,
                                                  If(to_district == 7, 22, 0)))))),
                             If(from_district == 6,
                                If(to_district == 0, 26,
                                   If(to_district == 1, 13,
                                      If(to_district == 2, 19,
                                         If(to_district == 3, 20,
                                            If(to_district == 4, 18,
                                               If(to_district == 5, 10,
                                                  If(to_district == 6, 0,
                                                     If(to_district == 7, 22, 0)))))),
                                If(from_district == 7,
                                   If(to_district == 0, 10,
                                      If(to_district == 1, 19,
                                         If(to_district == 2, 13,
                                            If(to_district == 3, 7,
                                               If(to_district == 4, 16,
                                                  If(to_district == 5, 24,
                                                     If(to_district == 6, 22,
                                                        If(to_district == 7, 0, 0)))))),
                                   0))))) 

# Function to get available_start, available_end, required_duration for a friend index
def get_available_start(friend_index):
    return If(friend_index == 0, friends[0]['available_start'],
              If(friend_index == 1, friends[1]['available_start'],
                 If(friend_index == 2, friends[2]['available_start'],
                    If(friend_index == 3, friends[3]['available_start'],
                       If(friend_index == 4, friends[4]['available_start'],
                          If(friend_index == 5, friends[5]['available_start'],
                             If(friend_index == 6, friends[6]['available_start'], 0))))))

def get_available_end(friend_index):
    return If(friend_index == 0, friends[0]['available_end'],
              If(friend_index == 1, friends[1]['available_end'],
                 If(friend_index == 2, friends[2]['available_end'],
                    If(friend_index == 3, friends[3]['available_end'],
                       If(friend_index == 4, friends[4]['available_end'],
                          If(friend_index == 5, friends[5]['available_end'],
                             If(friend_index == 6, friends[6]['available_end'], 0))))))

def get_required_duration(friend_index):
    return If(friend_index == 0, friends[0]['required_duration'],
              If(friend_index == 1, friends[1]['required_duration'],
                 If(friend_index == 2, friends[2]['required_duration'],
                    If(friend_index == 3, friends[3]['required_duration'],
                       If(friend_index == 4, friends[4]['required_duration'],
                          If(friend_index == 5, friends[5]['required_duration'],
                             If(friend_index == 6, friends[6]['required_duration'], 0))))))

# Add constraints for each position
for i in range(positions):
    f = friends_vars[i]
    s = start_vars[i]
    e = end_vars[i]
    solver.add(Implies(f != -1, 
                        And(
                            # Start time >= previous_end + travel_time
                            If(i == 0,
                               s >= 540 + get_travel_time(0, get_district(f)),
                               s >= end_vars[i-1] + get_travel_time(get_district(friends_vars[i-1]), get_district(f))
                            ),
                            # Start time >= available_start
                            s >= get_available_start(f),
                            # End time <= available_end
                            e <= get_available_end(f),
                            # Duration >= required_duration
                            e - s >= get_required_duration(f)
                        )))

# Maximize the number of friends met
num_friends = Sum([If(f != -1, 1, 0) for f in friends_vars])
solver.maximize(num_friends)

# Check if the problem is satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the itinerary
    itinerary = []
    for i in range(positions):
        f = model.eval(friends_vars[i])
        if f != -1:
            # Get the friend's name
            friend_index = f.as_long()
            name = friends[friend_index]['name']
            # Get start and end times in minutes
            start = model.eval(start_vars[i]).as_long()
            end = model.eval(end_vars[i]).as_long()
            # Convert to HH:MM format
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            start_time = to_time_str(start)
            end_time = to_time_str(end)
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    # Filter out any None entries (if any)
    filtered_itinerary = [entry for entry in itinerary if entry is not None]
    # Sort by start time to ensure chronological order
    filtered_itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": filtered_itinerary}))
else:
    print("No solution found.")