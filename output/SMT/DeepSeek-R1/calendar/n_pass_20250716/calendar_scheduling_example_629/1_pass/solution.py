from z3 import *

def main():
    # Work hours: 9:00 to 17:00 -> 8 hours = 480 minutes
    total_minutes_in_work_day = 480
    
    # Only Tuesday is considered (Margaret doesn't want Monday)
    s = Int('start_time_tuesday')
    
    solver = Solver()
    
    # Constraints for work hours and Margaret's preference (after 14:30)
    solver.add(s >= 330)        # 14:30 is 5.5 hours from 9:00 -> 5.5*60 = 330 minutes
    solver.add(s + 30 <= total_minutes_in_work_day)  # Meeting ends by 17:00 (480 minutes)
    
    # Blocked intervals for Tuesday (in minutes from 9:00)
    # Margaret: 12:00 to 12:30 -> 180 to 210 minutes
    margaret_blocked_start = 180
    margaret_blocked_end = 210
    
    # Alexis: 14:00 to 16:30 -> 300 to 450 minutes
    alexis_blocked_start = 300
    alexis_blocked_end = 450
    
    # Non-overlap constraints for Margaret's blocked interval
    # Meeting must end by the start of the blocked interval or start after the end
    solver.add(Or(s + 30 <= margaret_blocked_start, s >= margaret_blocked_end))
    
    # Non-overlap constraints for Alexis's blocked interval
    solver.add(Or(s + 30 <= alexis_blocked_start, s >= alexis_blocked_end))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Calculate start time in HH:MM
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        print(f"Tuesday {start_time} {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()