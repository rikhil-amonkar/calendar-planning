from z3 import Solver, Int, Or, And

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes - 540  # Subtract 9:00 in minutes (9*60=540)

def main():
    s = Solver()
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 and last 30 minutes
    s.add(start >= 0)          # 9:00
    s.add(start <= 450)        # 17:00 - 30 minutes = 16:30 (450 minutes from 9:00)
    
    # Busy times for each participant (converted to minutes from 9:00)
    busy_times = {
        "Stephanie": [(time_to_minutes("11:00"), time_to_minutes("11:30")), 
                      (time_to_minutes("14:30"), time_to_minutes("15:00"))],
        "Joe": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                (time_to_minutes("10:00"), time_to_minutes("12:00")),
                (time_to_minutes("12:30"), time_to_minutes("13:00")),
                (time_to_minutes("14:00"), time_to_minutes("17:00"))],
        "Diana": [(time_to_minutes("9:00"), time_to_minutes("10:30")),
                  (time_to_minutes("11:30"), time_to_minutes("12:00")),
                  (time_to_minutes("13:00"), time_to_minutes("14:00")),
                  (time_to_minutes("14:30"), time_to_minutes("15:30")),
                  (time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Deborah": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                    (time_to_minutes("10:30"), time_to_minutes("12:00")),
                    (time_to_minutes("12:30"), time_to_minutes("13:00")),
                    (time_to_minutes("13:30"), time_to_minutes("14:00")),
                    (time_to_minutes("14:30"), time_to_minutes("15:30")),
                    (time_to_minutes("16:00"), time_to_minutes("16:30"))]
    }
    
    # Add constraints for each participant's busy times
    for person, intervals in busy_times.items():
        for (busy_start, busy_end) in intervals:
            s.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday {start_hour:02d}:{start_minute:02d} to {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()