from z3 import *

# Days indexing: 0=Monday,...,4=Friday
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

def time_to_slot(t):  # t like "HH:MM"
    h, m = map(int, t.split(":"))
    return (h - 9) * 2 + (0 if m == 0 else 1)

def add_busy(busy_map, person, day_idx, start_str, end_str):
    s = time_to_slot(start_str)
    e = time_to_slot(end_str)
    for slot in range(s, e):  # half-hour slots covering [start, end)
        busy_map[person][day_idx].add(slot)

# Initialize busy maps
people = ["Bryan", "Nicholas"]
busy = {p: {d: set() for d in range(5)} for p in people}

# Bryan's schedule:
# Thursday: 9:30-10:00, 12:30-13:00
add_busy(busy, "Bryan", 3, "09:30", "10:00")
add_busy(busy, "Bryan", 3, "12:30", "13:00")
# Friday: 10:30-11:00, 14:00-14:30
add_busy(busy, "Bryan", 4, "10:30", "11:00")
add_busy(busy, "Bryan", 4, "14:00", "14:30")

# Nicholas's schedule:
# Monday: 11:30-12:00, 13:00-15:30
add_busy(busy, "Nicholas", 0, "11:30", "12:00")
add_busy(busy, "Nicholas", 0, "13:00", "15:30")
# Tuesday: 9:00-9:30, 11:00-13:30, 14:00-16:30
add_busy(busy, "Nicholas", 1, "09:00", "09:30")
add_busy(busy, "Nicholas", 1, "11:00", "13:30")
add_busy(busy, "Nicholas", 1, "14:00", "16:30")
# Wednesday: 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:00-14:30, 15:00-16:30
add_busy(busy, "Nicholas", 2, "09:00", "09:30")
add_busy(busy, "Nicholas", 2, "10:00", "11:00")
add_busy(busy, "Nicholas", 2, "11:30", "13:30")
add_busy(busy, "Nicholas", 2, "14:00", "14:30")
add_busy(busy, "Nicholas", 2, "15:00", "16:30")
# Thursday: 10:30-11:30, 12:00-12:30, 15:00-15:30, 16:30-17:00
add_busy(busy, "Nicholas", 3, "10:30", "11:30")
add_busy(busy, "Nicholas", 3, "12:00", "12:30")
add_busy(busy, "Nicholas", 3, "15:00", "15:30")
add_busy(busy, "Nicholas", 3, "16:30", "17:00")
# Friday: 9:00-10:30, 11:00-12:00, 12:30-14:30, 15:30-16:00, 16:30-17:00
add_busy(busy, "Nicholas", 4, "09:00", "10:30")
add_busy(busy, "Nicholas", 4, "11:00", "12:00")
add_busy(busy, "Nicholas", 4, "12:30", "14:30")
add_busy(busy, "Nicholas", 4, "15:30", "16:00")
add_busy(busy, "Nicholas", 4, "16:30", "17:00")

# Z3 variables
day = Int('day')          # 0..4
start = Int('start')      # half-hour slot index, 0..14 (meeting is 2 slots = 1 hour)
meeting_slots = 2

opt = Optimize()
opt.add(And(day >= 0, day <= 4))
opt.add(And(start >= 0, start <= 16 - meeting_slots))

# No overlaps with busy times (meeting occupies start and start+1)
for person in people:
    for d in range(5):
        bset = busy[person][d]
        # For a given day, both slots must be free
        constraints = []
        for b in bset:
            constraints.append(start != b)
            constraints.append(start + 1 != b)
        opt.add(Implies(day == d, And(constraints) if constraints else True))

# Preferences (soft constraints):
# Bryan would like to avoid Tuesday.
# Nicholas would rather not meet on Monday and Thursday.
pref_penalties = []
pref_penalties.append(If(day == 1, 1, 0))  # Bryan avoid Tuesday
pref_penalties.append(If(day == 0, 1, 0))  # Nicholas avoid Monday
pref_penalties.append(If(day == 3, 1, 0))  # Nicholas avoid Thursday
total_penalty = Sum(pref_penalties)
opt.minimize(total_penalty)

# Tie-breaker: earliest start time if same penalty
opt.minimize(start)

assert opt.check() == sat
model = opt.model()

def slot_to_time(slot):
    minutes = 9*60 + slot*30
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

chosen_day = model[day].as_long()
chosen_start = model[start].as_long()
chosen_end = chosen_start + meeting_slots

print("SOLUTION:")
print(f"Day: {days[chosen_day]}")
print(f"Start Time: {slot_to_time(chosen_start)}")
print(f"End Time: {slot_to_time(chosen_end)}")