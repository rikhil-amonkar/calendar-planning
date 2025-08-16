from z3 import *

# Define friends data
friends = [
    {
        'name': 'Helen',
        'location': 8,  # North Beach
        'available_start': 11 * 60 + 0,  # 11:00 AM
        'available_end': 12 * 60 + 15,   # 12:15 PM
        'duration': 45,
    },
    {
        'name': 'Mary',
        'location': 7,  # Nob Hill
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 19 * 60 + 0,     # 7:00 PM
        'duration': 45,
    },
    {
        'name': 'Barbara',
        'location': 5,  # Alamo Square
        'available_start': 17 * 60 + 0,   # 5:00 PM
        'available_end': 19 * 60 + 0,     # 7:00 PM
        'duration': 120,
    },
    {
        'name': 'Emily',
        'location': 3,  # Fisherman's Wharf
        'available_start': 16 * 60 + 15,  # 4:15 PM
        'available_end': 19 * 60 + 0,     # 7:00 PM
        'duration': 30,
    },
    {
        'name': 'Mark',
        'location': 4,  # Marina District
        'available_start': 18 * 60 + 15,  # 6:15 PM
        'available_end': 19 * 60 + 45,    # 7:45 PM
        'duration': 75,
    },
    {
        'name': 'Laura',
        'location': 6,  # Sunset District
        'available_start': 19 * 60 + 0,   # 7:00 PM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'duration': 75,
    },
    {
        'name': 'Michelle',
        'location': 2,  # Golden Gate Park
        'available_start': 20 * 60 + 0,   # 8:00 PM
        'available_end': 21 * 60 + 0,     # 9:00 PM
        'duration': 15,
    },
]

# Define available_start, available_end, duration for each friend index
available_start_values = [f['available_start'] for f in friends]
available_end_values = [f['available_end'] for f in friends]
duration_values = [f['duration'] for f in friends]

# Define functions to get available_start, available_end, duration based on friend index
def get_available_start(fi):
    return If(fi == 0, available_start_values[0],
        If(fi == 1, available_start_values[1],
            If(fi == 2, available_start_values[2],
                If(fi == 3, available_start_values[3],
                    If(fi == 4, available_start_values[4],
                        If(fi == 5, available_start_values[5],
                            If(fi == 6, available_start_values[6], -1)
                        )
                    )
                )
            )
        )
    )

def get_available_end(fi):
    return If(fi == 0, available_end_values[0],
        If(fi == 1, available_end_values[1],
            If(fi == 2, available_end_values[2],
                If(fi == 3, available_end_values[3],
                    If(fi == 4, available_end_values[4],
                        If(fi == 5, available_end_values[5],
                            If(fi == 6, available_end_values[6], -1)
                        )
                    )
                )
            )
        )
    )

def get_duration(fi):
    return If(fi == 0, duration_values[0],
        If(fi == 1, duration_values[1],
            If(fi == 2, duration_values[2],
                If(fi == 3, duration_values[3],
                    If(fi == 4, duration_values[4],
                        If(fi == 5, duration_values[5],
                            If(fi == 6, duration_values[6], -1)
                        )
                    )
                )
            )
        )
    )

# Define function to get location based on friend index
def get_location(fi):
    return If(fi == 0, 8,
        If(fi == 1, 7,
            If(fi == 2, 5,
                If(fi == 3, 3,
                    If(fi == 4, 4,
                        If(fi == 5, 6,
                            If(fi == 6, 2, -1)
                        )
                    )
                )
            )
        )
    )

# Define travel_time_matrix
travel_time_matrix = [
    # Presidio to all
    [0, 11, 12, 19, 11, 19, 15, 18, 18],  # Presidio (0)
    # Pacific Heights to all
    [11, 0, 15, 13, 6, 10, 21, 8, 9],  # Pacific Heights (1)
    # Golden Gate Park to all
    [12, 16, 0, 24, 16, 9, 10, 20, 23],  # Golden Gate Park (2)
    # Fisherman's Wharf to all
    [17, 12, 25, 0, 9, 21, 27, 11, 6],  # Fisherman's Wharf (3)
    # Marina District to all
    [10, 7, 18, 10, 0, 15, 19, 12, 11],  # Marina District (4)
    # Alamo Square to all
    [17, 10, 9, 19, 15, 0, 16, 11, 15],  # Alamo Square (5)
    # Sunset District to all
    [16, 21, 11, 29, 21, 17, 0, 27, 28],  # Sunset District (6)
    # Nob Hill to all
    [17, 8, 17, 10, 11, 11, 24, 0, 8],  # Nob Hill (7)
    # North Beach to all
    [17, 8, 22, 5, 9, 16, 27, 7, 0],  # North Beach (8)
]

# Define get_travel_time function
def get_travel_time(pl, cl):
    return If(pl == 0,
        If(cl == 0, 0,
            If(cl == 1, 11,
                If(cl == 2, 12,
                    If(cl == 3, 19,
                        If(cl == 4, 11,
                            If(cl == 5, 19,
                                If(cl == 6, 15,
                                    If(cl == 7, 18,
                                        If(cl == 8, 18, -1)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        ),
        If(pl == 1,
            If(cl == 0, 11,
                If(cl == 1, 0,
                    If(cl == 2, 15,
                        If(cl == 3, 13,
                            If(cl == 4, 6,
                                If(cl == 5, 10,
                                    If(cl == 6, 21,
                                        If(cl == 7, 8,
                                            If(cl == 8, 9, -1)
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            ),
            If(pl == 2,
                If(cl == 0, 12,
                    If(cl == 1, 16,
                        If(cl == 2, 0,
                            If(cl == 3, 24,
                                If(cl == 4, 16,
                                    If(cl == 5, 9,
                                        If(cl == 6, 10,
                                            If(cl == 7, 20,
                                                If(cl == 8, 23, -1)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                ),
                If(pl == 3,
                    If(cl == 0, 17,
                        If(cl == 1, 12,
                            If(cl == 2, 25,
                                If(cl == 3, 0,
                                    If(cl == 4, 9,
                                        If(cl == 5, 21,
                                            If(cl == 6, 27,
                                                If(cl == 7, 11,
                                                    If(cl == 8, 6, -1)
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    ),
                    If(pl == 4,
                        If(cl == 0, 10,
                            If(cl == 1, 7,
                                If(cl == 2, 18,
                                    If(cl == 3, 10,
                                        If(cl == 4, 0,
                                            If(cl == 5, 15,
                                                If(cl == 6, 19,
                                                    If(cl == 7, 12,
                                                        If(cl == 8, 11, -1)
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        ),
                        If(pl == 5,
                            If(cl == 0, 17,
                                If(cl == 1, 10,
                                    If(cl == 2, 9,
                                        If(cl == 3, 19,
                                            If(cl == 4, 15,
                                                If(cl == 5, 0,
                                                    If(cl == 6, 16,
                                                        If(cl == 7, 11,
                                                            If(cl == 8, 15, -1)
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            ),
                            If(pl == 6,
                                If(cl == 0, 16,
                                    If(cl == 1, 21,
                                        If(cl == 2, 11,
                                            If(cl == 3, 29,
                                                If(cl == 4, 21,
                                                    If(cl == 5, 17,
                                                        If(cl == 6, 0,
                                                            If(cl == 7, 27,
                                                                If(cl == 8, 28, -1)
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                ),
                                If(pl == 7,
                                    If(cl == 0, 17,
                                        If(cl == 1, 8,
                                            If(cl == 2, 17,
                                                If(cl == 3, 10,
                                                    If(cl == 4, 11,
                                                        If(cl == 5, 11,
                                                            If(cl == 6, 24,
                                                                If(cl == 7, 0,
                                                                    If(cl == 8, 8, -1)
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    If(pl == 8,
                                        If(cl == 0, 17,
                                            If(cl == 1, 8,
                                                If(cl == 2, 22,
                                                    If(cl == 3, 5,
                                                        If(cl == 4, 9,
                                                            If(cl == 5, 16,
                                                                If(cl == 6, 27,
                                                                    If(cl == 7, 7,
                                                                        If(cl == 8, 0, -1)
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        ),
                                        -1
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )

# Create variables for each step
max_meetings = 7
friends_count = len(friends)
friend_vars = [Int('friend_%d' % i) for i in range(max_meetings)]
start_time_vars = [Int('start_time_%d' % i) for i in range(max_meetings)]

opt = Optimize()

# Constraints: friend_i is between -1 and friends_count-1
for i in range(max_meetings):
    opt.add(And(friend_vars[i] >= -1, friend_vars[i] <= friends_count - 1))

# Constraints: no two steps have the same friend (excluding -1)
for i in range(max_meetings):
    for j in range(i + 1, max_meetings):
        opt.add(Or(friend_vars[i] == -1, friend_vars[j] == -1, friend_vars[i] != friend_vars[j]))

# Constraints for each step
for i in range(max_meetings):
    if i == 0:
        # First step: from Presidio (0)
        fi = friend_vars[i]
        loc = get_location(fi)
        travel_time = get_travel_time(0, loc)
        arrival_time = 540 + travel_time  # 9:00 AM is 540 mins
        opt.add(Implies(fi != -1, start_time_vars[i] >= arrival_time))
        opt.add(Implies(fi != -1, start_time_vars[i] >= get_available_start(fi)))
        opt.add(Implies(fi != -1, start_time_vars[i] + get_duration(fi) <= get_available_end(fi)))
    else:
        # Subsequent steps
        prev_fi = friend_vars[i-1]
        curr_fi = friend_vars[i]
        # If both are not -1
        prev_loc = get_location(prev_fi)
        curr_loc = get_location(curr_fi)
        travel_time = get_travel_time(prev_loc, curr_loc)
        prev_start_time = start_time_vars[i-1]
        prev_duration = get_duration(prev_fi)
        arrival_time = prev_start_time + prev_duration + travel_time
        opt.add(Implies(And(curr_fi != -1, prev_fi != -1), start_time_vars[i] >= arrival_time))
        opt.add(Implies(And(curr_fi != -1, prev_fi != -1), start_time_vars[i] >= get_available_start(curr_fi)))
        opt.add(Implies(And(curr_fi != -1, prev_fi != -1), start_time_vars[i] + get_duration(curr_fi) <= get_available_end(curr_fi)))

# Objective: maximize the number of friends met
total_met = Sum([If(friend_vars[i] != -1, 1, 0) for i in range(max_meetings)])
opt.maximize(total_met)

# Check if the problem is satisfiable
if opt.check() == sat:
    model = opt.model()
    # Extract the itinerary
    itinerary = []
    for i in range(max_meetings):
        fi = model.eval(friend_vars[i])
        if fi != -1:
            friend_index = fi.as_long()
            start_time = model.eval(start_time_vars[i]).as_long()
            end_time = start_time + duration_values[friend_index]
            # Convert to HH:MM format
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
            friend_name = friends[friend_index]['name']
            itinerary.append({"action": "meet", "person": friend_name, "start_time": start_str, "end_time": end_str})
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")