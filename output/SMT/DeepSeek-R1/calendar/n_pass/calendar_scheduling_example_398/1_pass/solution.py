from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00)
    S = Int('S')
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Total available time: 9:00 (0 min) to 17:00 (480 min)
    # Meeting must end by 480 min -> S <= 480 - 30 = 450
    s.add(S >= 0)
    s.add(S <= 450)
    
    # Define busy intervals for each person in minutes (relative to 9:00)
    # Each interval is (start, end) in minutes [start inclusive, end exclusive)
    busy_times = {
        'Doris': [
            (0, 120),    # 9:00-11:00
            (270, 300),  # 13:30-14:00
            (420, 450)   # 16:00-16:30
        ],
        'Theresa': [
            (60, 180)    # 10:00-12:00
        ],
        'Terry': [
            (30, 60),    # 9:30-10:00
            (150, 180),  # 11:30-12:00
            (210, 240),  # 12:30-13:00
            (270, 300),  # 13:30-14:00
            (330, 360),  # 14:30-15:00
            (390, 480)   # 15:30-17:00
        ],
        'Carolyn': [
            (0, 90),     # 9:00-10:30
            (120, 150),  # 11:00-11:30
            (180, 240),  # 12:00-13:00
            (270, 330),  # 13:30-14:30
            (360, 480)   # 15:00-17:00
        ],
        'Kyle': [
            (0, 30),     # 9:00-9:30
            (150, 180),  # 11:30-12:00
            (210, 240),  # 12:30-13:00
            (330, 480)   # 14:30-17:00
        ]
    }
    
    # Christian has no meetings, so no constraints
    
    # Add constraints for each person's busy intervals
    for person, intervals in busy_times.items():
        for (A, B) in intervals:
            # The meeting [S, S+30) must not overlap with [A, B)
            # So either: meeting ends before A starts, or meeting starts after B ends
            s.add(Or(S + meeting_duration <= A, S >= B))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # End time is start time + 30 minutes
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()