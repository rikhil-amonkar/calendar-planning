# Define the possible slots on Tuesday
possible_slots = [(1, 390)]  # (day, start_time in minutes since 9:00)

# Convert the slots to human-readable format
solutions = []
for d, st in possible_slots:
    meeting_day = "Monday" if d == 0 else "Tuesday"
    meeting_start_time_minutes = st
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time = f"{9 + (meeting_start_time_minutes + 30) // 60}:{(meeting_start_time_minutes + 30) % 60:02}"
    solutions.append((meeting_day, meeting_start_time, meeting_end_time))

# Print the solutions
if solutions:
    print(f"SOLUTION:\nDay: {solutions[0][0]}\nStart Time: {solutions[0][1]}\nEnd Time: {solutions[0][2]}")
else:
    print("No solution found")