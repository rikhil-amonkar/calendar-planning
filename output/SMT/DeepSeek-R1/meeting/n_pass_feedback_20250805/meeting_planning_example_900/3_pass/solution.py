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
    # Set slot to -1 if not scheduled (dummy value)
    opt.add(If(scheduled[i], slot[i] >= min_slot, slot[i] == -1))

# Constraint: No overlapping meetings for attendees
for a in set().union(*[set(m.attendees) for m in meetings]):
    for i in range(num_meetings):
        for j in range(i + 1, num_meetings):
            if a in meetings[i].attendees and a in meetings[j].attendees:
                # Both meetings can't be scheduled at same time if they share an attendee
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
    
    # Validate the solution
    valid = True
    scheduled_slots = {}
    for i, m in enumerate(meetings):
        if is_true(model.evaluate(scheduled[i])):
            slot_val = model.evaluate(slot[i]).as_long()
            # Check if slot is available
            if slot_val not in m.available_slots:
                print(f"ERROR: Meeting {m.id} scheduled at unavailable slot {slot_val}")
                valid = False
            
            # Check for attendee conflicts
            for a in m.attendees:
                if a in scheduled_slots:
                    if slot_val in scheduled_slots[a]:
                        print(f"ERROR: Attendee {a} has overlapping meetings at slot {slot_val}")
                        valid = False
                    scheduled_slots[a].add(slot_val)
                else:
                    scheduled_slots[a] = {slot_val}
    
    if valid:
        print("Solution validated: No conflicts found")
    else:
        print("Solution has conflicts!")
else:
    print("No solution found")