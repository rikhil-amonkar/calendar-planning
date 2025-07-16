# Correct start time calculation
start_time_minutes_from_midnight = 547
start_time_hours = start_time_minutes_from_midnight // 60
start_time_minutes = start_time_minutes_from_midnight % 60
print(f"SOLUTION: You should start meeting Barbara at {start_time_hours:02}:{start_time_minutes:02} AM.")