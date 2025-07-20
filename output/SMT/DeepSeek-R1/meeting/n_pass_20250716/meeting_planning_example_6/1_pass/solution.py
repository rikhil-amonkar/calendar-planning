from z3 import *

def minutes_to_time(t):
    total_minutes = 540 + t  # 540 minutes = 9:00 AM
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

s = Solver()

t_depart_fw = Int('t_depart_fw')
t_depart_nh = Int('t_depart_nh')

t_arrive_nh = t_depart_fw + 11

s.add(t_depart_fw >= 0)
s.add(t_depart_nh >= t_arrive_nh)

s_start = If(t_arrive_nh < 315, 315, t_arrive_nh)
e_end = If(t_depart_nh > 645, 645, t_depart_nh)

meeting_duration = If(e_end > s_start, e_end - s_start, 0)
s.add(meeting_duration >= 90)

if s.check() == sat:
    m = s.model()
    dep_fw = m[t_depart_fw].as_long()
    dep_nh = m[t_depart_nh].as_long()
    arr_nh = dep_fw + 11

    time_dep_fw = minutes_to_time(dep_fw)
    time_arr_nh = minutes_to_time(arr_nh)
    time_dep_nh = minutes_to_time(dep_nh)

    s_start_val = max(arr_nh, 315)
    e_end_val = min(dep_nh, 645)
    actual_duration = max(0, e_end_val - s_start_val)

    print("SOLUTION:")
    print(f"Leave Fisherman's Wharf at: {time_dep_fw}")
    print(f"Arrive at Nob Hill at: {time_arr_nh}")
    print(f"Leave Nob Hill at: {time_dep_nh}")
    print(f"Meeting duration: {actual_duration} minutes")
else:
    print("No solution found")