from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Meeting duration in minutes
    duration = 30
    # Total available time in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_time = 480
    # Start time variable (minutes after 9:00)
    start = Int('start')
    # Constraint: start time must be between 0 and (480 - duration)
    s.add(start >= 0, start <= total_time - duration)
    
    # Convert busy times to minutes for each participant
    # Andrea: no meetings -> no constraints
    
    # Jack: [9:00-9:30, 14:00-14:30]
    jack_busy = [(0, 30), (5*60, 5*60 + 30)]  # [0,30) and [300,330)
    
    # Madison: [9:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00]
    madison_busy = [
        (30, 90),           # 9:30-10:30
        (4*60, 5*60),       # 13:00-14:00 -> [240, 300)
        (6*60, 6*60 + 30),  # 15:00-15:30 -> [360, 390)
        (7*60 + 30, 8*60)   # 16:30-17:00 -> [450, 480)
    ]
    
    # Rachel: [9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00]
    rachel_busy = [
        (30, 90),           # 9:30-10:30
        (2*60, 2*60 + 30),  # 11:00-11:30 -> [120,150)
        (3*60, 4*60 + 30),  # 12:00-13:30 -> [180,270)
        (5*60 + 30, 6*60 + 30), # 14:30-15:30 -> [330,390)
        (7*60, 8*60)        # 16:00-17:00 -> [420,480)
    ]
    
    # Douglas: [9:00-11:30, 12:00-16:30]
    douglas_busy = [
        (0, 2*60 + 30),     # 9:00-11:30 -> [0,150)
        (3*60, 7*60 + 30)   # 12:00-16:30 -> [180,450)
    ]
    
    # Ryan: [9:00-9:30, 13:00-14:00, 14:30-17:00]
    ryan_busy = [
        (0, 30),            # 9:00-9:30
        (4*60, 5*60),       # 13:00-14:00 -> [240,300)
        (5*60 + 30, 8*60)   # 14:30-17:00 -> [330,480)
    ]
    
    # Add constraints for each participant's busy intervals
    participants = {
        "Jack": jack_busy,
        "Madison": madison_busy,
        "Rachel": rachel_busy,
        "Douglas": douglas_busy,
        "Ryan": ryan_busy
    }
    
    for name, intervals in participants.items():
        for (b_start, b_end) in intervals:
            # Meeting must be either entirely before or entirely after the busy interval
            s.add(Or(start + duration <= b_start, start >= b_end))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model.eval(start).as_long()
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        # Print the meeting time
        print(f"Meeting can be scheduled from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()