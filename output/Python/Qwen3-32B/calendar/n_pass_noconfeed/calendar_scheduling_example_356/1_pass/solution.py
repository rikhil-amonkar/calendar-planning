participants = {
    'Katherine': [(720, 750), (780, 870)],
    'Rebecca': [],
    'Julie': [(540, 570), (630, 660), (810, 840), (900, 930)],
    'Angela': [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)],
    'Nicholas': [(570, 660), (690, 810), (840, 960), (990, 1020)],
    'Carl': [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)],
}

def is_free(t, participants):
    for busy_intervals in participants.values():
        for s, e in busy_intervals:
            if t < e and t + 30 > s:
                return False
    return True

start_work = 540  # 9:00 AM
end_work = 1020    # 5:00 PM
selected_t = None

# First check for times after 15:00 (900 minutes)
for t in range(start_work, end_work - 30 + 1):
    if t >= 900 and is_free(t, participants):
        selected_t = t
        break  # take the earliest one

# If not found, check earlier times
if selected_t is None:
    for t in range(start_work, end_work - 30 + 1):
        if t < 900 and is_free(t, participants):
            selected_t = t
            break

def to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

start_time = selected_t
end_time = selected_t + 30
start_str = to_time_str(start_time)
end_str = to_time_str(end_time)

print(f"{start_str}:{end_str} Monday")