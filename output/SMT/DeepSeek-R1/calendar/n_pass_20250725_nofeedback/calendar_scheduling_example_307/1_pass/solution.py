from z3 import *

def main():
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        total_minutes = (hours - 9) * 60 + minutes
        return total_minutes

    # Busy intervals for each participant
    # Ronald: wide open -> no busy intervals
    ronald = []
    
    stephen = []
    stephen.append(('10:00', '10:30'))
    stephen.append(('12:00', '12:30'))
    
    brittany = []
    brittany.append(('11:00', '11:30'))
    brittany.append(('13:30', '14:00'))
    brittany.append(('15:30', '16:00'))
    brittany.append(('16:30', '17:00'))
    
    dorothy = []
    dorothy.append(('9:00', '9:30'))
    dorothy.append(('10:00', '10:30'))
    dorothy.append(('11:00', '12:30'))
    dorothy.append(('13:00', '15:00'))
    dorothy.append(('15:30', '17:00'))
    
    rebecca = []
    rebecca.append(('9:30', '10:30'))
    rebecca.append(('11:00', '11:30'))
    rebecca.append(('12:00', '12:30'))
    rebecca.append(('13:00', '17:00'))
    
    jordan = []
    jordan.append(('9:00', '9:30'))
    jordan.append(('10:00', '11:00'))
    jordan.append(('11:30', '12:00'))
    jordan.append(('13:00', '15:00'))
    jordan.append(('15:30', '16:30'))
    
    participants = {
        "Ronald": ronald,
        "Stephen": stephen,
        "Brittany": brittany,
        "Dorothy": dorothy,
        "Rebecca": rebecca,
        "Jordan": jordan
    }
    
    # Convert all busy intervals to minutes
    busy_intervals = []
    for person, intervals in participants.items():
        for interval in intervals:
            start_min = time_to_minutes(interval[0])
            end_min = time_to_minutes(interval[1])
            busy_intervals.append((start_min, end_min))
    
    # Set up Z3 solver
    s = Solver()
    start_var = Int('start')
    meeting_duration = 30
    
    # Constraint: start must be between 0 and 450 (inclusive of 0, exclusive of 450? Actually 450 inclusive because 450+30=480 is allowed end at 17:00)
    s.add(start_var >= 0)
    s.add(start_var <= 450)  # 450 + 30 = 480 (17:00)
    
    # For each busy interval, the meeting must not overlap
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(
            start_var + meeting_duration <= busy_start,
            start_var >= busy_end
        ))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_var].as_long()
        
        # Convert start_minutes back to HH:MM
        total_minutes_from_9 = start_minutes
        hours = 9 + total_minutes_from_9 // 60
        minutes = total_minutes_from_9 % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        hours_end = 9 + end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()