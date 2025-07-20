from z3 import *

def main():
    # Initialize Z3 solver and variable
    s = Solver()
    start_time_minutes = Int('start_time_minutes')
    
    # Work hours: 9:00 (0 minutes) to 17:00 (480 minutes)
    s.add(start_time_minutes >= 0)
    s.add(start_time_minutes + 30 <= 480)  # Meeting duration constraint
    
    # Frank's constraint: meeting must end by 9:30 (30 minutes from 9:00)
    s.add(start_time_minutes + 30 <= 30)
    
    # Define busy slots in minutes from 9:00
    emily_busy = [
        (60, 90),    # 10:00-10:30
        (150, 210),  # 11:30-12:30
        (300, 360),  # 14:00-15:00
        (420, 450)   # 16:00-16:30
    ]
    melissa_busy = [
        (30, 60),    # 9:30-10:00
        (330, 360)   # 14:30-15:00
    ]
    frank_busy = [
        (60, 90),    # 10:00-10:30
        (120, 150),  # 11:00-11:30
        (210, 240),  # 12:30-13:00
        (270, 330),  # 13:30-14:30
        (360, 420),  # 15:00-16:00
        (450, 480)   # 16:30-17:00
    ]
    
    # Function to add non-overlap constraints for a participant
    def add_non_overlap(busy_slots):
        for a, b in busy_slots:
            s.add(Or(start_time_minutes + 30 <= a, start_time_minutes >= b))
    
    add_non_overlap(emily_busy)
    add_non_overlap(melissa_busy)
    add_non_overlap(frank_busy)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_min = model[start_time_minutes].as_long()
        
        # Convert start time to HH:MM format
        total_min_start = 9 * 60 + start_min
        hours_start = total_min_start // 60
        minutes_start = total_min_start % 60
        start_time_str = f"{hours_start}:{minutes_start:02d}"
        
        # Convert end time to HH:MM format
        end_min = start_min + 30
        total_min_end = 9 * 60 + end_min
        hours_end = total_min_end // 60
        minutes_end = total_min_end % 60
        end_time_str = f"{hours_end}:{minutes_end:02d}"
        
        # Output the meeting time
        print("Monday", start_time_str, end_time_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()