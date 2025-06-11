from z3 import *

def time_to_slot_index(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    total_minutes = (hour - 9) * 60 + minute
    return total_minutes // 30

susan_events = [
    ('Monday', ["12:30", "13:00"]),
    ('Monday', ["13:30", "14:00"]),
    ('Tuesday', ["11:30", "12:00"]),
    ('Wednesday', ["9:30", "10:30"]),
    ('Wednesday', ["14:00", "14:30"]),
    ('Wednesday', ["15:30", "16:30"])
]

sandra_events = [
    ('Monday', ["9:00", "13:00"]),
    ('Monday', ["14:00", "15:00"]),
    ('Monday', ["16:00", "16:30"]),
    ('Tuesday', ["9:00", "9:30"]),
    ('Tuesday', ["10:30", "12:00"]),
    ('Tuesday', ["12:30", "13:30"]),
    ('Tuesday', ["14:00", "14:30"]),
    ('Tuesday', ["16:00", "17:00"]),
    ('Wednesday', ["9:00", "11:30"]),
    ('Wednesday', ["12:00", "12:30"]),
    ('Wednesday', ["13:00", "17:00"])
]

day_map = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
free_susan = [[True for _ in range(16)] for _ in range(3)]
free_sandra = [[True for _ in range(16)] for _ in range(3)]

for event in susan_events:
    day_name, interval = event
    start_str, end_str = interval
    start_slot = time_to_slot_index(start_str)
    end_slot = time_to_slot_index(end_str)
    d_index = day_map[day_name]
    for slot_index in range(start_slot, end_slot):
        if slot_index < 16:
            free_susan[d_index][slot_index] = False

for event in sandra_events:
    day_name, interval = event
    start_str, end_str = interval
    start_slot = time_to_slot_index(start_str)
    end_slot = time_to_slot_index(end_str)
    d_index = day_map[day_name]
    for slot_index in range(start_slot, end_slot):
        if slot_index < 16:
            free_sandra[d_index][slot_index] = False

# Apply Sandra's constraint: cannot meet on Monday after 16:00 (blocks both 16:00-16:30 and 16:30-17:00)
free_sandra[0][14] = False  # 16:00-16:30
free_sandra[0][15] = False  # 16:30-17:00

free_both = [[free_susan[d][i] and free_sandra[d][i] for i in range(16)] for d in range(3)]

day = Int('day')
slot = Int('slot')

constraints = []
for d in range(3):
    for i in range(16):
        if free_both[d][i]:
            constraints.append(And(day == d, slot == i))

if not constraints:
    print("No solution exists")
else:
    s1 = Solver()
    s1.add(Or(constraints))
    s1.add(day != 1)  # Avoid Tuesday (day 1)
    
    if s1.check() == sat:
        m = s1.model()
    else:
        s2 = Solver()
        s2.add(Or(constraints))
        s2.check()
        m = s2.model()
    
    d_val = m[day].as_long()
    s_val = m[slot].as_long()
    
    day_names = ["Monday", "Tuesday", "Wednesday"]
    start_minutes = 9 * 60 + 30 * s_val
    end_minutes = start_minutes + 30
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    start_str = f"{start_hour}:{start_minute:02d}"
    end_str = f"{end_hour}:{end_minute:02d}"
    
    print(f"('{day_names[d_val]}', '{start_str}', '{end_str}')")