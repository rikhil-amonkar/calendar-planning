def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) - 9) * 60 + int(m)

def minutes_to_time(m):
    h = 9 + m // 60
    m_min = m % 60
    return f"{h}:{m_min:02d}"

participants = ['Shirley', 'Jacob', 'Stephen', 'Margaret', 'Mason']
busy_times = {
    'Shirley': [['10:30', '11:00'], ['12:00', '12:30']],
    'Jacob': [['9:00', '9:30'], ['10:00', '10:30'], ['11:00', '11:30'], ['12:30', '13:30'], ['14:30', '15:00']],
    'Stephen': [['11:30', '12:00'], ['12:30', '13:00']],
    'Margaret': [['9:00', '9:30'], ['10:30', '12:30'], ['13:00', '13:30'], ['15:00', '15:30'], ['16:30', '17:00']],
    'Mason': [['9:00', '10:00'], ['10:30', '11:00'], ['11:30', '12:30'], ['13:00', '13:30'], ['14:00', '14:30'], ['16:30', '17:00']]
}

work_end_minutes = 480
busy_minutes = {}
for p in participants:
    converted = []
    for s, e in busy_times[p]:
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        converted.append([s_min, e_min])
    converted.sort(key=lambda x: x[0])
    busy_minutes[p] = converted

free_intervals = {}
for p in participants:
    intervals = busy_minutes[p]
    free = []
    current = 0
    for s, e in intervals:
        if current < s:
            free.append([current, s])
        current = e
    if current < work_end_minutes:
        free.append([current, work_end_minutes])
    free_intervals[p] = free

common = free_intervals['Shirley']
for p in ['Jacob', 'Stephen', 'Margaret', 'Mason']:
    next_free = free_intervals[p]
    new_common = []
    for c_int in common:
        c_start, c_end = c_int
        for n_int in next_free:
            n_start, n_end = n_int
            low = max(c_start, n_start)
            high = min(c_end, n_end)
            if low < high:
                new_common.append([low, high])
    common = new_common

margaret_constraint = 330
candidate_intervals = []
for start, end in common:
    adj_start = max(start, margaret_constraint)
    if end - adj_start >= 30:
        candidate_intervals.append([adj_start, end])

if candidate_intervals:
    candidate_intervals.sort(key=lambda x: x[0])
    meeting_start = candidate_intervals[0][0]
    meeting_end = meeting_start + 30
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    print("No suitable time found")