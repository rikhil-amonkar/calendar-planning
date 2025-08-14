from z3 import *

# Define the variables for the day and time slots
day = BoolVector('day', 2)  # day[0] for Monday, day[1] for Tuesday

# Define the time slots from 9:00 to 17:00 in 30-minute increments
time_slots = BoolVector('time_slot', 16)  # time_slot[0] for 9:00-9:30, ..., time_slot[15] for 16:30-17:00

# Define the meeting duration as one time slot (30 minutes)
meeting_duration = 1

# Define the constraints for Jean's availability
jean_constraints = [
    Or(Not(day[1]), Not(time_slots[7])),  # Jean is busy on Tuesday from 11:30 to 12:00 (time_slot[7])
    Or(Not(day[1]), Not(time_slots[11]))  # Jean is busy on Tuesday from 16:00 to 16:30 (time_slot[11])
]

# Define the constraints for Doris's availability
doris_constraints = [
    Or(Not(day[0]), Not(time_slots[0])),  # Doris is busy on Monday from 9:00 to 11:30 (time_slots[0] and time_slots[1])
    Or(Not(day[0]), Not(time_slots[1])),
    Or(Not(day[0]), Not(time_slots[4])),  # Doris is busy on Monday from 12:00 to 12:30 (time_slot[4])
    Or(Not(day[0]), Not(time_slots[7])),  # Doris is busy on Monday from 13:30 to 16:00 (time_slots[7] to time_slots[11])
    Or(Not(day[0]), Not(time_slots[8])),
    Or(Not(day[0]), Not(time_slots[9])),
    Or(Not(day[0]), Not(time_slots[10])),
    Or(Not(day[0]), Not(time_slots[11])),
    Or(Not(day[0]), Not(time_slots[12])),  # Doris is busy on Monday from 16:30 to 17:00 (time_slot[12])
    [Or(Not(day[1]), Not(time_slots[i])) for i in range(16)]  # Doris is busy on Tuesday all day
]

# Flatten the list of constraints for Doris
doris_constraints = [c for sublist in doris_constraints for c in (sublist if isinstance(sublist, list) else [sublist])]

# Doris's preference to not meet after 14:00 on Monday
doris_preference = [
    Or(Not(day[0]), Not(time_slots[i])) for i in range(9, 16)  # Slots from 14:00 to 17:00 (time_slots[9] to time_slots[15])
]

# Create the solver
solver = Solver()

# Add constraints to the solver
solver.add(jean_constraints + doris_constraints)

# Add preference as soft constraints (not strictly necessary but can help find preferred solutions)
solver.add(doris_preference)

# Define the condition that exactly one day is chosen
solver.add(Or(day))
solver.add([Implies(day[i], Not(day[j])) for i in range(2) for j in range(i+1, 2)])

# Define the condition that exactly one valid time slot is chosen for a 30-minute meeting
valid_meeting_slots = []
for i in range(16 - meeting_duration + 1):
    valid_meeting_slots.append(And(time_slots[i], Not(time_slots[i + meeting_duration])))

solver.add(Or(valid_meeting_slots))
solver.add([Implies(slot, Not(other)) for slot in valid_meeting_slots for other in valid_meeting_slots if slot != other])

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    # Determine the day
    if m.evaluate(day[0]):
        chosen_day = "Monday"
    else:
        chosen_day = "Tuesday"
    
    # Determine the start time
    for i in range(16 - meeting_duration + 1):
        if m.evaluate(time_slots[i]):
            start_time_slot = i
            break
    
    start_hour = 9 + start_time_slot // 2
    start_minute = (start_time_slot % 2) * 30
    end_hour = start_hour + (meeting_duration // 2)
    end_minute = start_minute + (meeting_duration % 2) * 30
    
    # Format the times
    start_time = f"{start_hour:02}:{start_minute:02}"
    end_time = f"{end_hour:02}:{end_minute:02}"
    
    print(f"SOLUTION:\nDay: {chosen_day}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")