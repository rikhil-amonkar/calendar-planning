from z3 import *

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

# Create Z3 variables
scheduled = [Bool(f'scheduled_{i}') for i in range(num_meetings)]
slot = [Int(f'slot_{i}') for i in range(num_meetings)]

# Create an Optimize instance
opt = Optimize()

# Create set constraints for available slots
for i, m in enumerate(meetings):
    available_set = EmptySet(IntSort())
    for s in m.available_slots:
        available_set = SetAdd(available_set, s)
    opt.add(Implies(scheduled[i], InSet(slot[i], available_set)))
    opt.add(Implies(Not(scheduled[i]), slot[i] == -1))

# Build attendee-meeting mapping
attendee_meetings = {}
for i, m in enumerate(meetings):
    for a in m.attendees:
        if a not in attendee_meetings:
            attendee_meetings[a] = []
        attendee_meetings[a].append(i)

# Add conflict constraints for attendees
for a, meeting_ids in attendee_meetings.items():
    for i in range(len(meeting_ids)):
        for j in range(i + 1, len(meeting_ids)):
            idx1 = meeting_ids[i]
            idx2 = meeting_ids[j]
            opt.add(Implies(
                And(scheduled[idx1], scheduled[idx2]),
                slot[idx1] != slot[idx2]
            ))

# Objective: Maximize scheduled meetings
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
            # Check slot availability
            if slot_val not in m.available_slots:
                print(f"ERROR: Meeting {m.id} scheduled at unavailable slot {slot_val}")
                valid = False
            
            # Check attendee conflicts
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
    # Should never happen since scheduling nothing is always valid
    print("Total meetings scheduled: 0")
    print("Schedule: {}")