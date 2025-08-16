from z3 import *
import json

# Define friends' data
available_start = [435, 540, 660, 480, 165, 660, 405]  # Paul, Carol, Patricia, Karen, Nancy, Jeffrey, Matthew
available_end = [735, 675, 750, 600, 780, 705, 765]
min_duration = [60, 120, 75, 45, 30, 45, 75]
person_to_location = [1, 2, 3, 4, 5, 6, 7]  # 0: Paul (Nob Hill=1), etc.

MAX_MEETINGS = 7

# Create variables
person_vars = [Int(f'person_{i}') for i in range(MAX_MEETINGS)]
start_vars = [Int(f'start_{i}') for i in range(MAX_MEETINGS)]
end_vars = [Int(f'end_{i}') for i in range(MAX_MEETINGS)]
location_vars = [Int(f'location_{i}') for i in range(MAX_MEETINGS)]

solver = Optimize()

# Constraints for person to location mapping
for i in range(MAX_MEETINGS):
    solver.add(Or(person_vars[i] == -1, And([person_vars[i] >= 0, person_vars[i] <= 6])))
    for p in range(7):
        solver.add(Implies(person_vars[i] == p, location_vars[i] == person_to_location[p]))

# Helper function for travel time
def get_travel_time(prev_loc, current_loc):
    return If(
        prev_loc == 0,
        If(current_loc == 0, 0,
            If(current_loc == 1, 20,
                If(current_loc == 2, 17,
                    If(current_loc == 3, 18,
                        If(current_loc == 4, 20,
                            If(current_loc == 5, 31,
                                If(current_loc == 6, 23,
                                    If(current_loc == 7, 23, 0)
                                )
                            )
                        )
                    )
                )
            )
        ),
        If(prev_loc == 1,
            If(current_loc == 0, 19,
                If(current_loc == 1, 0,
                    If(current_loc == 2, 7,
                        If(current_loc == 3, 6,
                            If(current_loc == 4, 17,
                                If(current_loc == 5, 17,
                                    If(current_loc == 6, 8,
                                        If(current_loc == 7, 5, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 2,
            If(current_loc == 0, 15,
                If(current_loc == 1, 9,
                    If(current_loc == 2, 0,
                        If(current_loc == 3, 7,
                            If(current_loc == 4, 19,
                                If(current_loc == 5, 24,
                                    If(current_loc == 6, 15,
                                        If(current_loc == 7, 13, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 3,
            If(current_loc == 0, 22,
                If(current_loc == 1, 8,
                    If(current_loc == 2, 7,
                        If(current_loc == 3, 0,
                            If(current_loc == 4, 22,
                                If(current_loc == 5, 19,
                                    If(current_loc == 6, 10,
                                        If(current_loc == 7, 7, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 4,
            If(current_loc == 0, 19,
                If(current_loc == 1, 16,
                    If(current_loc == 2, 19,
                        If(current_loc == 3, 20,
                            If(current_loc == 4, 0,
                                If(current_loc == 5, 20,
                                    If(current_loc == 6, 16,
                                        If(current_loc == 7, 18, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 5,
            If(current_loc == 0, 31,
                If(current_loc == 1, 18,
                    If(current_loc == 2, 22,
                        If(current_loc == 3, 21,
                            If(current_loc == 4, 21,
                                If(current_loc == 5, 0,
                                    If(current_loc == 6, 11,
                                        If(current_loc == 7, 14, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 6,
            If(current_loc == 0, 22,
                If(current_loc == 1, 8,
                    If(current_loc == 2, 12,
                        If(current_loc == 3, 11,
                            If(current_loc == 4, 16,
                                If(current_loc == 5, 11,
                                    If(current_loc == 6, 0,
                                        If(current_loc == 7, 7, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        If(prev_loc == 7,
            If(current_loc == 0, 23,
                If(current_loc == 1, 5,
                    If(current_loc == 2, 11,
                        If(current_loc == 3, 9,
                            If(current_loc == 4, 21,
                                If(current_loc == 5, 14,
                                    If(current_loc == 6, 7,
                                        If(current_loc == 7, 0, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            ),
        0
    )

# Constraints for start and end times
for i in range(MAX_MEETINGS):
    if i == 0:
        travel_time = get_travel_time(0, location_vars[i])
        solver.add(start_vars[i] == travel_time)
    else:
        travel_time = get_travel_time(location_vars[i-1], location_vars[i])
        solver.add(start_vars[i] == end_vars[i-1] + travel_time)

# Constraints for meeting validity
for i in range(MAX_MEETINGS):
    p = person_vars[i]
    s = start_vars[i]
    e = end_vars[i]
    solver.add(Implies(p != -1, e == s + min_duration[p]))
    solver.add(Implies(p != -1, s >= available_start[p]))
    solver.add(Implies(p != -1, e <= available_end[p]))

# Constraints for unique persons
for i in range(MAX_MEETINGS):
    for j in range(i+1, MAX_MEETINGS):
        solver.add(Or(person_vars[i] == -1, person_vars[j] == -1, person_vars[i] != person_vars[j]))

# Optimization goal
num_met = Sum([If(person_vars[i] != -1, 1, 0) for i in range(MAX_MEETINGS)])
solver.maximize(num_met)

# Check if solution exists
if solver.check() == sat:
    model = solver.model()
    meetings = []
    for i in range(MAX_MEETINGS):
        p_val = model[person_vars[i]].as_long()
        if p_val != -1:
            start = model[start_vars[i]].as_long()
            end = model[end_vars[i]].as_long()
            def to_time(m):
                hours = 9 + m // 60
                mins = m % 60
                return f"{hours:02d}:{mins:02d}"
            person_name = ["Paul", "Carol", "Patricia", "Karen", "Nancy", "Jeffrey", "Matthew"][p_val]
            meetings.append({
                "action": "meet",
                "person": person_name,
                "start_time": to_time(start),
                "end_time": to_time(end)
            })
    print("SOLUTION:")
    print(json.dumps({"itinerary": meetings}))
else:
    print("No solution found.")