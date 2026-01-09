from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all times to minutes since midnight for easier calculation
    # Daniel: free all day
    daniel_busy = []
    
    # Kathleen: 14:30 to 15:30
    kathleen_busy = [(14*60 + 30, 15*60 + 30)]
    
    # Carolyn: 12:00-12:30, 13:00-13:30
    carolyn_busy = [(12*60, 12*60 + 30), (13*60, 13*60 + 30)]
    
    # Roger: free all day, but prefers not before 12:30
    roger_busy = []
    roger_preference = 12*60 + 30
    
    # Cheryl: 9:00-9:30, 10:00-11:30, 12:30-13:30, 14:00-17:00
    cheryl_busy = [(9*60, 9*60 + 30), (10*60, 11*60 + 30), 
                   (12*60 + 30, 13*60 + 30), (14*60, 17*60)]
    
    # Virginia: 9:30-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30, 16:00-17:00
    virginia_busy = [(9*60 + 30, 11*60 + 30), (12*60, 12*60 + 30),
                     (13*60, 13*60 + 30), (14*60 + 30, 15*60 + 30),
                     (16*60, 17*60)]
    
    # Angela: 9:30-10:00, 10:30-11:30, 12:00-12:30, 13:00-13:30, 14:00-16:30
    angela_busy = [(9*60 + 30, 10*60), (10*60 + 30, 11*60 + 30),
                   (12*60, 12*60 + 30), (13*60, 13*60 + 30),
                   (14*60, 16*60 + 30)]
    
    # All participants
    participants = [
        ('Daniel', daniel_busy),
        ('Kathleen', kathleen_busy),
        ('Carolyn', carolyn_busy),
        ('Roger', roger_busy),
        ('Cheryl', cheryl_busy),
        ('Virginia', virginia_busy),
        ('Angela', angela_busy)
    ]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = range(work_start, work_end - meeting_duration + 1, 15)
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Constraint: meeting must not conflict with anyone's schedule
    def no_conflict(start_time, busy_slots):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in busy_slots:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    for name, busy_slots in participants:
        problem.addConstraint(
            lambda start_time, bs=busy_slots: no_conflict(start_time, bs),
            ['start_time']
        )
    
    # Roger's preference: not before 12:30
    problem.addConstraint(
        lambda start_time: start_time >= roger_preference,
        ['start_time']
    )
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort by start time (earliest first)
        solutions.sort(key=lambda x: x['start_time'])
        best_solution = solutions[0]
        start_minutes = best_solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()