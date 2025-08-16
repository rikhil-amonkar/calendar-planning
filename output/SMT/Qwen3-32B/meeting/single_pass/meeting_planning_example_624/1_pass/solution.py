from z3 import *

# Define friends
friends = [
    {'name': 'Karen', 'location': 3, 'available_start': 435, 'available_end': 840, 'duration': 75},
    {'name': 'Deborah', 'location': 5, 'available_start': 720, 'available_end': 900, 'duration': 105},
    {'name': 'Laura', 'location': 2, 'available_start': 705, 'available_end': 1290, 'duration': 60},
    {'name': 'Elizabeth', 'location': 4, 'available_start': 735, 'available_end': 1290, 'duration': 75},
    {'name': 'Jason', 'location': 6, 'available_start': 885, 'available_end': 1140, 'duration': 90},
    {'name': 'Steven', 'location': 7, 'available_start': 885, 'available_end': 1110, 'duration': 120},
    {'name': 'Carol', 'location': 1, 'available_start': 1290, 'available_end': 1350, 'duration': 60},
]

# Define travel times between locations (0 to 7)
travel_times = {
    (0, 1): 7,
    (0, 2): 24,
    (0, 3): 13,
    (0, 4): 23,
    (0, 5): 10,
    (0, 6): 24,
    (0, 7): 19,
    (1, 0): 7,
    (1, 2): 23,
    (1, 3): 6,
    (1, 4): 19,
    (1, 5): 5,
    (1, 6): 19,
    (1, 7): 17,
    (2, 0): 25,
    (2, 1): 22,
    (2, 3): 26,
    (2, 4): 12,
    (2, 5): 20,
    (2, 6): 6,
    (2, 7): 7,
    (3, 0): 11,
    (3, 1): 6,
    (3, 2): 24,
    (3, 4): 20,
    (3, 5): 8,
    (3, 6): 20,
    (3, 7): 18,
    (4, 0): 23,
    (4, 1): 19,
    (4, 2): 8,
    (4, 3): 22,
    (4, 5): 17,
    (4, 6): 3,
    (4, 7): 7,
    (5, 0): 9,
    (5, 1): 5,
    (5, 2): 19,
    (5, 3): 8,
    (5, 4): 16,
    (5, 6): 15,
    (5, 7): 13,
    (6, 0): 22,
    (6, 1): 18,
    (6, 2): 5,
    (6, 3): 22,
    (6, 4): 6,
    (6, 5): 16,
    (6, 7): 4,
    (7, 0): 21,
    (7, 1): 17,
    (7, 2): 7,
    (7, 3): 21,
    (7, 4): 9,
    (7, 5): 15,
    (7, 6): 5,
}

def solve():
    for num_friends in range(7, 0, -1):
        solver = Solver()
        friend_vars = [Int(f'friend_{i}') for i in range(7)]
        arrival_time_vars = [Int(f'arrival_{i}') for i in range(7)]

        # Constraints: friend_vars are between 0-7
        for f in friend_vars:
            solver.add(And(f >= 0, f <= 7))

        # Constraint: exactly num_friends are used
        used_count = Sum([If(f == 7, 0, 1) for f in friend_vars])
        solver.add(used_count == num_friends)

        # Constraint: unique friends
        for i in range(7):
            for j in range(i + 1, 7):
                solver.add(Or(friend_vars[i] == 7, friend_vars[j] == 7, friend_vars[i] != friend_vars[j]))

        # Constraint: if step i is used, all previous steps are used
        for i in range(1, 7):
            for j in range(i):
                solver.add(Implies(friend_vars[i] != 7, friend_vars[j] != 7))

        # Add arrival time constraints
        for i in range(7):
            # Get loc_i, available_start_i, available_end_i, duration_i
            loc_i = If(friend_vars[i] == 0, 3,
                       If(friend_vars[i] == 1, 5,
                       If(friend_vars[i] == 2, 2,
                       If(friend_vars[i] == 3, 4,
                       If(friend_vars[i] == 4, 6,
                       If(friend_vars[i] == 5, 7,
                       If(friend_vars[i] == 6, 1, 0)))))))
            available_start_i = If(friend_vars[i] == 0, 435,
                                   If(friend_vars[i] == 1, 720,
                                   If(friend_vars[i] == 2, 705,
                                   If(friend_vars[i] == 3, 735,
                                   If(friend_vars[i] == 4, 885,
                                   If(friend_vars[i] == 5, 885,
                                   If(friend_vars[i] == 6, 1290, 0)))))))
            available_end_i = If(friend_vars[i] == 0, 840,
                                 If(friend_vars[i] == 1, 900,
                                 If(friend_vars[i] == 2, 1290,
                                 If(friend_vars[i] == 3, 1290,
                                 If(friend_vars[i] == 4, 1140,
                                 If(friend_vars[i] == 5, 1110,
                                 If(friend_vars[i] == 6, 1350, 0)))))))
            duration_i = If(friend_vars[i] == 0, 75,
                            If(friend_vars[i] == 1, 105,
                            If(friend_vars[i] == 2, 60,
                            If(friend_vars[i] == 3, 75,
                            If(friend_vars[i] == 4, 90,
                            If(friend_vars[i] == 5, 120,
                            If(friend_vars[i] == 6, 60, 0))))))

            # Add constraints if friend is used
            solver.add(Implies(friend_vars[i] != 7, arrival_time_vars[i] >= available_start_i))
            solver.add(Implies(friend_vars[i] != 7, arrival_time_vars[i] + duration_i <= available_end_i))

            if i == 0:
                # Travel time from 0 to loc_i
                travel_time_0_to_loc_i = If(loc_i == 1, 7,
                                            If(loc_i == 2, 24,
                                            If(loc_i == 3, 13,
                                            If(loc_i == 4, 23,
                                            If(loc_i == 5, 10,
                                            If(loc_i == 6, 24,
                                            If(loc_i == 7, 19, 0)))))))
                solver.add(Implies(friend_vars[i] != 7, arrival_time_vars[i] == 540 + travel_time_0_to_loc_i))
            else:
                # Previous step's variables
                loc_prev = If(friend_vars[i-1] == 0, 3,
                              If(friend_vars[i-1] == 1, 5,
                              If(friend_vars[i-1] == 2, 2,
                              If(friend_vars[i-1] == 3, 4,
                              If(friend_vars[i-1] == 4, 6,
                              If(friend_vars[i-1] == 5, 7,
                              If(friend_vars[i-1] == 6, 1, 0)))))))
                duration_prev = If(friend_vars[i-1] == 0, 75,
                                   If(friend_vars[i-1] == 1, 105,
                                   If(friend_vars[i-1] == 2, 60,
                                   If(friend_vars[i-1] == 3, 75,
                                   If(friend_vars[i-1] == 4, 90,
                                   If(friend_vars[i-1] == 5, 120,
                                   If(friend_vars[i-1] == 6, 60, 0))))))

                # Travel time between loc_prev and loc_i
                travel_time_prev_to_current = 0
                for a in range(1, 8):
                    for b in range(1, 8):
                        travel_time_prev_to_current = If(And(loc_prev == a, loc_i == b), travel_times[(a, b)], travel_time_prev_to_current)

                # Add constraint for arrival_time
                solver.add(Implies(friend_vars[i] != 7, arrival_time_vars[i] >= arrival_time_vars[i-1] + duration_prev + travel_time_prev_to_current))

        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            for i in range(7):
                f_val = model.evaluate(friend_vars[i])
                if f_val != 7:
                    friend_index = f_val.as_long()
                    arrival_time = model.evaluate(arrival_time_vars[i]).as_long()
                    duration = friends[friend_index]['duration']
                    end_time = arrival_time + duration
                    start_h = arrival_time // 60
                    start_m = arrival_time % 60
                    end_h = end_time // 60
                    end_m = end_time % 60
                    start_str = f"{start_h:02d}:{start_m:02d}"
                    end_str = f"{end_h:02d}:{end_m:02d}"
                    itinerary.append({"action": "meet", "person": friends[friend_index]['name'], "start_time": start_str, "end_time": end_str})
            return {"itinerary": itinerary}
    return {"itinerary": []}

# Call the solve function and print the result
result = solve()
print(result)