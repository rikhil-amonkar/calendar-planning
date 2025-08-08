from z3 import *

# Define the meeting structure
class Meeting:
    def __init__(self, id, attendees, available_slots):
        self.id = id
        self.attendees = attendees
        self.available_slots = available_slots

# Example meetings data
meetings = [
    Meeting(0, [0, 1], [1, 2, 3]),
    Meeting(1, [0, 2], [2, 3, 4]),
    Meeting(2, [1, 2], [3, 4, 5])
]

num_meetings = len(meetings)

# Collect all time slots from all meetings
all_slots = set()
for m in meetings:
    all_slots.update(m.available_slots)

if not all_slots:
    print("No available slots. Total meetings scheduled: 0")
    exit(0)

min_slot = min(all_slots)
max_slot = max(all_slots)

# Create Z3 variables
scheduled = [Bool(f'scheduled_{i}') for i in range(num_meetings)]
slot = [Int(f'slot_{i}') for i in range(num_meetings)]

# Create an Optimize instance
opt = Optimize()

# Constraint: If a meeting is scheduled, it must be in one of its available slots
for i, m in enumerate(meetings):
    opt.add(Implies(scheduled[i], Or([slot[i] == s for s in m.available_slots])))
    opt.add(slot[i] >= min_slot, slot[i] <= max_slot)

# Constraint: Conflicting meetings (shared attendees) cannot overlap
for i in range(num_meetings):
    for j in range(i + 1, num_meetings):
        if set(meetings[i].attendees) & set(meetings[j].attendees):
            opt.add(Implies(And(scheduled[i], scheduled[j]), slot[i] != slot[j]))

# Objective: Maximize the number of scheduled meetings
total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(num_meetings)])
opt.maximize(total_meetings)

# Solve and output results
if opt.check() == sat:
    model = opt.model()
    total_scheduled = model.evaluate(total_meetings)
    print(f"Total meetings scheduled: {total_scheduled}")
    
    schedule = {}
    for i, m in enumerate(meetings):
        if is_true(model.evaluate(scheduled[i])):
            s_val = model.evaluate(slot[i])
            schedule[m.id] = s_val.as_long() if isinstance(s_val, IntNumRef) else s_val
    print("Schedule:", schedule)
else:
    print("No solution found")