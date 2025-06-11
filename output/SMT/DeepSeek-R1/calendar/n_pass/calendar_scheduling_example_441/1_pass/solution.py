from z3 import *

def main():
    # Define the start variable (in minutes from 9:00)
    start = Int('start')
    
    # Constraints: meeting must be within 9:00 to 17:00 (0 to 480 minutes from 9:00), and duration 30 minutes
    constraints = [start >= 0, start <= 450]  # 450 because 480 - 30 = 450
    
    # Convert time string to minutes since 9:00
    def to_minutes(time_str):
        h, m = time_str.split(':')
        total_minutes = int(h) * 60 + int(m)
        return total_minutes - 540  # 9:00 is 540 minutes from midnight
    
    # Participants and their busy intervals
    participants = {
        "Joan": ["11:30 to 12:00", "14:30 to 15:00"],
        "Megan": ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"],
        "Austin": [],
        "Betty": ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"],
        "Judith": ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"],
        "Terry": ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"],
        "Kathryn": ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"]
    }
    
    # Add constraints for each participant's busy intervals
    for person, intervals in participants.items():
        for interval in intervals:
            parts = interval.split(' to ')
            if len(parts) < 2:
                continue
            start_busy = to_minutes(parts[0])
            end_busy = to_minutes(parts[1])
            constraints.append(Or(start + 30 <= start_busy, start >= end_busy))
    
    # Solve the constraints
    s = Solver()
    s.add(constraints)
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Convert start_val back to time string
        total_minutes_from_midnight = start_val + 540
        hours = total_minutes_from_midnight // 60
        minutes = total_minutes_from_midnight % 60
        start_time_str = f"{hours}:{minutes:02d}"
        
        end_val = start_val + 30
        total_minutes_end = end_val + 540
        hours_end = total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time_str = f"{hours_end}:{minutes_end:02d}"
        
        # Output the meeting time
        print("Monday")
        print(start_time_str)
        print(end_time_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()