def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02}:{mins:02}"

participants = {
    "juan": {
        "busy": [(540, 630), (930, 960)],  # 9:00-10:30, 15:30-16:00
        "max_end": 960  # Can't meet after 16:00
    },
    "marilyn": {
        "busy": [(600, 630), (750, 780)]  # 11:00-11:30, 12:30-13:00
    },
    "ronald": {
        "busy": [(540, 630), (720, 750), (780, 810), (840, 990)]  # 9:00-10:30, 12:00-12:30, 13:00-13:30, 14:00-16:30
    }
}

duration = 30
work_start = 540   # 9:00
work_end = 1020    # 17:00

for start in range(work_start, work_end - duration + 1, 30):
    end = start + duration
    # Check global work hours
    if end > work_end:
        continue
    
    # Check Juan's special constraint
    if end > participants["juan"]["max_end"]:
        continue
    
    # Check Juan's availability
    juan_conflict = any(start < busy_end and end > busy_start for busy_start, busy_end in participants["juan"]["busy"])
    if juan_conflict:
        continue
    
    # Check Marilyn's availability
    marilyn_conflict = any(start < busy_end and end > busy_start for busy_start, busy_end in participants["marilyn"]["busy"])
    if marilyn_conflict:
        continue
    
    # Check Ronald's availability
    ronald_conflict = any(start < busy_end and end > busy_start for busy_start, busy_end in participants["ronald"]["busy"])
    if ronald_conflict:
        continue
    
    # Found valid slot
    print(f"Monday:{to_time(start)}:{to_time(end)}")
    exit()

# Fallback if no slot found (though problem states solution exists)
print("No valid time found")