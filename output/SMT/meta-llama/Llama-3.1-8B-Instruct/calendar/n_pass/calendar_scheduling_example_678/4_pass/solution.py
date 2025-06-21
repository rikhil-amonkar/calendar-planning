# Add constraints for Russell's schedule
for time in russell_schedule:
    solver.add(Or(start_time + meeting_duration <= time[0], start_time >= time[1]))
    
# Add constraints for Alexander's schedule
for time in alexander_schedule:
    solver.add(Or(start_time + meeting_duration <= float(time[0]), start_time >= float(time[1])))