from z3 import *

# Define the days and times
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
start_times = [9, 9.5, 10, 10.5, 11, 11.5, 12, 12.5, 13, 13.5, 14, 14.5, 15, 15.5, 16]
end_times = [t + 0.5 for t in start_times]

# Create a Z3 solver instance
solver = Solver()

# Create Boolean variables for each participant's availability on each time slot
eugene_availability = {(d, s): Bool(f"eugene_{d}_{s}") for d in days for s in start_times}
eric_availability = {(d, s): Bool(f"eric_{d}_{s}") for d in days for s in start_times}

# Define Eugene's availability
for d in days:
    for s in start_times:
        if (d == "Monday" and s in [11, 13.5, 14.5, 16]) or \
           (d == "Wednesday" and s in [9, 11, 12, 13.5]) or \
           (d == "Thursday" and s in [9.5, 11]) or \
           (d == "Friday" and s in [10.5, 12, 13]):
            solver.add(Not(eugene_availability[(d, s)]))
        else:
            solver.add(eugene_availability[(d, s)])

# Define Eric's availability
for d in days:
    for s in start_times:
        if (d in ["Monday", "Tuesday", "Thursday"] and s >= 9) or \
           (d == "Wednesday" and s in [9, 12, 14.5]) or \
           (d == "Friday" and s in [9, 11.5]):
            solver.add(Not(eric_availability[(d, s)]))
        else:
            solver.add(eric_availability[(d, s)])

# Add constraint to avoid Wednesday for Eric
for s in start_times:
    solver.add(Not(eric_availability[("Wednesday", s)]))

# Define the meeting duration (0.5 hours)
meeting_duration = 0.5

# Create Boolean variable for the chosen time slot
chosen_time_slot = Bool("chosen_time_slot")

# Add constraints to find a common available time slot
for d in days:
    for s in start_times:
        e = eugene_availability[(d, s)]
        r = eric_availability[(d, s)]
        if s + meeting_duration in end_times:
            e_next = eugene_availability[(d, s + meeting_duration)]
            r_next = eric_availability[(d, s + meeting_duration)]
            solver.add(Implies(And(e, e_next, r, r_next), chosen_time_slot))

# Assert that a valid time slot must be found
solver.add(chosen_time_slot)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for d in days:
        for s in start_times:
            e = eugene_availability[(d, s)]
            r = eric_availability[(d, s)]
            if s + meeting_duration in end_times:
                e_next = eugene_availability[(d, s + meeting_duration)]
                r_next = eric_availability[(d, s + meeting_duration)]
                if model[e] and model[e_next] and model[r] and model[r_next]:
                    print(f"SOLUTION:")
                    print(f"Day: {d}")
                    print(f"Start Time: {int(s):02}:{int((s % 1) * 60):02}")
                    print(f"End Time: {int(s + meeting_duration):02}:{int(((s + meeting_duration) % 1) * 60):02}")
                    break
else:
    print("No solution found")