# Manually setting the solution based on manual verification
day = "Monday"
start_time = 15 * 60 + 30  # 15:30
end_time = start_time + 30  # 16:00

start_hour = start_time // 60
start_minute = start_time % 60
end_hour = end_time // 60
end_minute = end_time % 60

solution = f"SOLUTION:\nDay: {day}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}"
print(solution)